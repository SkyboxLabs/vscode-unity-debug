/*---------------------------------------------------------------------------------------------
 *  Copyright (c) Microsoft Corporation. All rights reserved.
 *  Copyright (c) Unity Technologies.
 *  Copyright (c) SkyBox Labs.
 *  Licensed under the MIT License. See License.txt in the project root for license information.
 *--------------------------------------------------------------------------------------------*/

using System;
using System.Collections.Generic;
using System.IO;
using System.Linq;
using System.Net;
using System.Net.Sockets;
using System.Threading;
using Microsoft.VisualStudio.Shared.VSCodeDebugProtocol;
using Microsoft.VisualStudio.Shared.VSCodeDebugProtocol.Messages;
using Mono.Debugging.Client;
using Mono.Debugging.Soft;
using MonoDevelop.Debugger.Soft.Unity;
using Newtonsoft.Json.Linq;

using Breakpoint = Microsoft.VisualStudio.Shared.VSCodeDebugProtocol.Messages.Breakpoint;
using DapThread = Microsoft.VisualStudio.Shared.VSCodeDebugProtocol.Messages.Thread;
using SdbBreakpoint = Mono.Debugging.Client.Breakpoint;
using SdbStackFrame = Mono.Debugging.Client.StackFrame;
using StackFrame = Microsoft.VisualStudio.Shared.VSCodeDebugProtocol.Messages.StackFrame;

namespace UnityDebug
{
    internal class UnityDebugSession : DebugAdapterBase
    {
        readonly string[] MONO_EXTENSIONS =
        {
            ".cs", ".csx",
            ".cake",
            ".fs", ".fsi", ".ml", ".mli", ".fsx", ".fsscript",
            ".hx"
        };
        const int MAX_CHILDREN = 100;
        const int MAX_CONNECTION_ATTEMPTS = 10;
        const int CONNECTION_ATTEMPT_INTERVAL = 500;

        AutoResetEvent m_ResumeEvent;
        bool m_DebuggeeExecuting;
        readonly object m_Lock = new object();
        SoftDebuggerSession m_Session;
        ProcessInfo m_ActiveProcess;
        Dictionary<string, Dictionary<int, SdbBreakpoint>> m_Breakpoints;
        List<Catchpoint> m_Catchpoints;
        DebuggerSessionOptions m_DebuggerSessionOptions;

        Handles<ObjectValue[]> m_VariableHandles;
        Handles<SdbStackFrame> m_FrameHandles;
        ObjectValue m_Exception;
        Dictionary<int, DapThread> m_SeenThreads;
        bool m_Terminated;
        IUnityDbgConnector unityDebugConnector;

        public bool LineStartsAt1 { get; private set; }
        public InitializeArguments.PathFormatValue PathFormat { get; private set; }

        public UnityDebugSession(Stream stdIn, Stream stdOut)
        {
            //Log.Write("Constructing UnityDebugSession");
            m_ResumeEvent = new AutoResetEvent(false);
            m_Breakpoints = new Dictionary<string, Dictionary<int, SdbBreakpoint>>();
            m_VariableHandles = new Handles<ObjectValue[]>();
            m_FrameHandles = new Handles<SdbStackFrame>();
            m_SeenThreads = new Dictionary<int, DapThread>();

            m_DebuggerSessionOptions = new DebuggerSessionOptions
            {
                EvaluationOptions = EvaluationOptions.DefaultOptions
            };

            m_Session = new UnityDebuggerSession();
            m_Session.Breakpoints = new BreakpointStore();

            m_Catchpoints = new List<Catchpoint>();

            //DebuggerLoggingService.CustomLogger = new CustomLogger();

            m_Session.ExceptionHandler = ex =>
            {
                return true;
            };

            m_Session.LogWriter = (isStdErr, text) =>
            {
                //SendOutput(isStdErr ? "stderr" : "stdout", text);
            };

            m_Session.TargetStopped += (sender, e) =>
            {
                if (e.Backtrace != null)
                {
                    Frame = e.Backtrace.GetFrame(0);
                }
                else
                {
                    this.ConsoleLog("e.Backtrace is null");
                }

                Stopped();
                this.Protocol.SendEvent(new StoppedEvent(StoppedEvent.ReasonValue.Step) {
                    ThreadId = (int)e.Thread.Id,
                });
                m_ResumeEvent.Set();
            };

            m_Session.TargetHitBreakpoint += (sender, e) =>
            {
                Frame = e.Backtrace.GetFrame(0);
                Stopped();
                this.Protocol.SendEvent(new StoppedEvent(StoppedEvent.ReasonValue.Breakpoint) {
                    ThreadId = (int)e.Thread.Id,
                });
                m_ResumeEvent.Set();
            };

            m_Session.TargetExceptionThrown += (sender, e) =>
            {
                Frame = e.Backtrace.GetFrame(0);
                for (var i = 0; i < e.Backtrace.FrameCount; i++)
                {
                    if (!e.Backtrace.GetFrame(i).IsExternalCode)
                    {
                        Frame = e.Backtrace.GetFrame(i);
                        break;
                    }
                }

                Stopped();
                var ex = DebuggerActiveException();
                if (ex != null)
                {
                    m_Exception = ex.Instance;
                    this.Protocol.SendEvent(new StoppedEvent(StoppedEvent.ReasonValue.Exception) {
                        ThreadId = (int)e.Thread.Id,
                        Text = ex.Message,
                    });
                }

                m_ResumeEvent.Set();
            };

            m_Session.TargetUnhandledException += (sender, e) =>
            {
                Stopped();
                var ex = DebuggerActiveException();
                if (ex != null)
                {
                    m_Exception = ex.Instance;
                    this.Protocol.SendEvent(new StoppedEvent(StoppedEvent.ReasonValue.Exception) {
                        ThreadId = (int)e.Thread.Id,
                        Text = ex.Message,
                    });
                }

                m_ResumeEvent.Set();
            };

            m_Session.TargetStarted += (sender, e) =>
            {
            };

            m_Session.TargetReady += (sender, e) =>
            {
                m_ActiveProcess = m_Session.GetProcesses().SingleOrDefault();
            };

            m_Session.TargetExited += (sender, e) =>
            {
                DebuggerKill();

                if (!this.m_Terminated)
                {
                    this.Protocol.SendEvent(new TerminatedEvent());
                    m_Terminated = true;
                }

                m_ResumeEvent.Set();
            };

            m_Session.TargetInterrupted += (sender, e) =>
            {
                m_ResumeEvent.Set();
            };

            m_Session.TargetEvent += (sender, e) => { };

            m_Session.TargetThreadStarted += (sender, e) =>
            {
                var tid = (int)e.Thread.Id;
                lock (m_SeenThreads)
                {
                    m_SeenThreads[tid] = new DapThread(tid, e.Thread.Name);
                }

                this.Protocol.SendEvent(new ThreadEvent(ThreadEvent.ReasonValue.Started, (int)tid));
            };

            m_Session.TargetThreadStopped += (sender, e) =>
            {
                var tid = (int)e.Thread.Id;
                lock (m_SeenThreads)
                {
                    m_SeenThreads.Remove(tid);
                }

                this.Protocol.SendEvent(new ThreadEvent(ThreadEvent.ReasonValue.Exited, (int)tid));
            };

            m_Session.OutputWriter = (isStdErr, text) =>
            {
                this.Protocol.SendEvent(new OutputEvent(text) {
                    Category = isStdErr ? OutputEvent.CategoryValue.Stderr : OutputEvent.CategoryValue.Stdout,
                });
            };

            this.InitializeProtocolClient(stdIn, stdOut);
        }

        public void Run()
        {
            this.Protocol.Run();
        }

        public SdbStackFrame Frame { get; set; }

        protected override InitializeResponse HandleInitializeRequest(InitializeArguments arguments)
        {
            var os = Environment.OSVersion;
            if (os.Platform != PlatformID.MacOSX && os.Platform != PlatformID.Unix && os.Platform != PlatformID.Win32NT)
            {
                throw new ProtocolException(
                    "notsupported",
                    3000,
                    "Mono Debug is not supported on this platform ({platform}).",
                    new Dictionary<string, object>() { { "platform", os.Platform.ToString() } },
                    showUser: true
                );
            }

            this.LineStartsAt1 = arguments.LinesStartAt1 ?? true;
            this.PathFormat = arguments.PathFormat ?? InitializeArguments.PathFormatValue.Path;

            this.ConsoleLog("Initializing...");
            this.Protocol.SendEvent(new InitializedEvent());

            return new InitializeResponse() {
                // This debug adapter does not support function breakpoints.
                //supportsFunctionBreakpoints: false,

                // This debug adapter support conditional breakpoints.
                SupportsConditionalBreakpoints = true,

                // This debug adapter does support a side effect free evaluate request for data hovers.
                SupportsEvaluateForHovers = true,

                SupportsExceptionOptions = true,

                SupportsHitConditionalBreakpoints = true,

                SupportsSetVariable = true

                // This debug adapter does not support exception breakpoint filters
                //exceptionBreakpointFilters: null,
            };
        }

        protected override AttachResponse HandleAttachRequest(AttachArguments arguments)
        {
            var config = arguments.ConfigurationProperties;
            JToken jValue;

            if (config.TryGetValue("__exceptionOptions", out jValue)) {
                this.SetExceptionBreakpoints(jValue.ToObject<dynamic>());
            }

            var projectRoot = config.TryGetValue("projectRoot", out jValue) ? jValue.Value<string>() : null;
            var platform = config.TryGetValue("platform", out jValue) ? jValue.Value<string>() : null;
            var address = config.TryGetValue("address", out jValue) ? jValue?.Value<string>() : "127.0.0.1";
            int port = config.TryGetValue("port", out jValue) ? jValue.Value<int>() : 0;

            switch (platform) {
                case null:
                case "editor":
                    if (!this.TryGetEditorDebugPort(projectRoot, out port)) {
                        throw new ProtocolException("Could not find editor process");
                    }
                    break;
                case "android":
                    if (port == 0) {
                        var targetType = AndroidConnectionTarget.Any;
                        switch ((string)config["android"]?.Value<string>("connection")) {
                            case "usb":
                                targetType = AndroidConnectionTarget.Usb;
                                break;
                            case "ip":
                                targetType = AndroidConnectionTarget.Ip;
                                break;
                        }

                        var env = ((JObject)config["env"])?.ToObject<Dictionary<string, string>>();
                        var adb = AndroidDebugBridge.GetAndroidDebugBridge(targetType, env);

                        if (adb == null) {
                            this.ConsoleLog("Could not locate adb. Make sure adb is available via PATH or set ANDROID_SDK_ROOT environment variable.");
                            throw new ProtocolException("Could not find adb");
                        }

                        if (!adb.TryPrepareConnection(out port, out var error)) {
                            this.ConsoleLog($"Could not establish device connection using adb: {error}");
                            throw new ProtocolException($"Could not connect to unity: {error}");
                        }
                    }
                    break;
            }

            this.ConsoleLog($"Attempting SDB connection to {address}:{port}");

            IPAddress hostIp;
            try {
                // Get first valid IPv4 address
                hostIp = Dns.GetHostAddresses(address)
                    .Where(ip => ip.AddressFamily == AddressFamily.InterNetwork)
                    .FirstOrDefault();
            }
            catch (Exception e) {
                throw new ProtocolException("Could not resolve SDB host", e);
            }

            this.Connect(hostIp, port);

            return new AttachResponse();

            /*
            var name = config["name"].ToString();

            Log.Write($"UnityDebug: Searching for Unity process '{name}'");
            SendOutput("stdout", "UnityDebug: Searching for Unity process '" + name + "'");

            var processes = UnityAttach.GetAttachableProcesses(name).ToArray();

            if (processes.Length == 0)
            {
                Log.Write($"Could not find target name '{name}'.");
                SendErrorResponse(response, 8001, "Could not find target name '{_name}'. Is it running?", new { _name = name });
                return;
            }

            UnityProcessInfo process;
            if (processes.Length == 1)
            {
                process = processes[0];
            }
            else
            {
                if (!name.Contains("Editor"))
                {
                    TooManyInstances(response, name, processes);
                    return;
                }

                string pathToEditorInstanceJson = GetString(config, "path");
                pathToEditorInstanceJson = CleanPath(pathToEditorInstanceJson);
                if (!File.Exists(pathToEditorInstanceJson))
                {
                    TooManyInstances(response, name, processes);
                    return;
                }

                var jObject = JObject.Parse(File.ReadAllText(pathToEditorInstanceJson.TrimStart('/')));
                var processId = jObject["process_id"].ToObject<int>();
                process = processes.First(p => p.Id == processId);
            }

            var attachInfo = UnityProcessDiscovery.GetUnityAttachInfo(process.Id, ref unityDebugConnector);

            Connect(attachInfo.Address, attachInfo.Port);

            Log.Write($"UnityDebug: Attached to Unity process '{process.Name}' ({process.Id})");
            SendOutput("stdout", "UnityDebug: Attached to Unity process '" + process.Name + "' (" + process.Id + ")\n");
            SendResponse(response);
            */
        }


        private bool TryGetEditorDebugPort(string projectRoot, out int port)
        {
            port = 0;

            if (projectRoot == null) {
                this.ConsoleLog("'projectRoot' configuration must be set when attaching to editor");
                return false;
            }

            this.ConsoleLog($"Checking for running editor for project at {projectRoot}");
            var pidFilePath = Path.Combine(projectRoot, "Library", "EditorInstance.json");

            if (!File.Exists(pidFilePath)) {
                return false;
            }

            var jObject = JObject.Parse(File.ReadAllText(pidFilePath));
            var pid = (jObject["process_id"].ToObject<int>() % 1000);

            this.ConsoleLog($"UnityDebug: Found editor with PID {pid}");

            port = 56000 + (pid % 1000);

            return true;
        }

        /*
        void TooManyInstances(Response response, string name, UnityProcessInfo[] processes)
        {
            Log.Write($"Multiple targets with name '{name}' running. Unable to connect.");
            SendErrorResponse(response, 8002, "Multiple targets with name '{_name}' running. Unable to connect.\n" +
                "Use \"Unity Attach Debugger\" from the command palette (View > Command Palette...) to specify which process to attach to.", new { _name = name });

            Log.Write($"UnityDebug: Multiple targets with name '{name}' running. Unable to connect.)");
            SendOutput("stdout", "UnityDebug: Multiple targets with name '" + name + "' running. Unable to connect.\n" +
                "Use \"Unity Attach Debugger\" from the command palette (View > Command Palette...) to specify which process to attach to.");

            foreach (var p in processes)
            {
                Log.Write($"UnityDebug: Found Unity process '{p.Name}' ({p.Id})");
                SendOutput("stdout", "UnityDebug: Found Unity process '" + p.Name + "' (" + p.Id + ")\n");
            }
        }
        */

        void Connect(IPAddress address, int port)
        {
            //Log.Write($"UnityDebug: Connect to: {address}:{port}");
            this.ConsoleLog($"Connecting to: {address}:{port}...");
            lock (m_Lock)
            {
                var args0 = new SoftDebuggerConnectArgs(string.Empty, address, port)
                {
                    MaxConnectionAttempts = MAX_CONNECTION_ATTEMPTS,
                    TimeBetweenConnectionAttempts = CONNECTION_ATTEMPT_INTERVAL
                };

                m_Session.Run(new SoftDebuggerStartInfo(args0), m_DebuggerSessionOptions);

                m_DebuggeeExecuting = true;
            }
        }

        //---- private ------------------------------------------

        protected override ConfigurationDoneResponse HandleConfigurationDoneRequest(ConfigurationDoneArguments arguments)
        {
            this.ConsoleLog("Configuration done");
            return new ConfigurationDoneResponse();
        }

        protected override DisconnectResponse HandleDisconnectRequest(DisconnectArguments arguments)
        {
            if (unityDebugConnector != null)
            {
                unityDebugConnector.OnDisconnect();
                unityDebugConnector = null;
            }

            lock (m_Lock)
            {
                if (m_Session != null)
                {
                    m_DebuggeeExecuting = true;
                    m_Breakpoints = null;
                    m_Session.Breakpoints.Clear();
                    m_Session.Continue();
                    m_Session.Detach();
                    m_Session.Adaptor.Dispose();
                    m_Session = null;
                }
            }

            this.ConsoleLog("Disconnected");
            return new DisconnectResponse();
        }

        protected override ContinueResponse HandleContinueRequest(ContinueArguments arguments)
        {
            WaitForSuspend();
            lock (m_Lock)
            {
                if (!(this.m_Session?.IsRunning ?? false) && !m_Session.HasExited) {
                    m_Session.Continue();
                    m_DebuggeeExecuting = true;
                }
                else {
                    this.ConsoleLog($"Did not continue: isRunning={this.m_Session?.IsRunning} exited={this.m_Session?.HasExited}");
                }
            }

            return new ContinueResponse();
        }

        protected override NextResponse HandleNextRequest(NextArguments arguments)
        {
            WaitForSuspend();
            lock (m_Lock)
            {
                if ((this.m_Session?.IsRunning ?? false) && !this.m_Session.HasExited) {
                    m_Session.NextLine();
                    m_DebuggeeExecuting = true;
                }
            }

            return new NextResponse();
        }

        protected override StepInResponse HandleStepInRequest(StepInArguments arguments)
        {
            WaitForSuspend();
            lock (m_Lock)
            {
                if ((this.m_Session?.IsRunning ?? false) && !this.m_Session.HasExited) {
                    m_Session.StepLine();
                    m_DebuggeeExecuting = true;
                }
            }

            return new StepInResponse();
        }

        protected override StepOutResponse HandleStepOutRequest(StepOutArguments arguments)
        {
            WaitForSuspend();
            lock (m_Lock)
            {
                if ((this.m_Session?.IsRunning ?? false) && !this.m_Session.HasExited) {
                    m_Session.Finish();
                    m_DebuggeeExecuting = true;
                }
            }

            return new StepOutResponse();
        }

        protected override PauseResponse HandlePauseRequest(PauseArguments arguments)
        {
            lock (m_Lock)
            {
                if (m_Session != null && m_Session.IsRunning)
                    m_Session.Stop();
            }
            return new PauseResponse();
        }

        protected override SetVariableResponse HandleSetVariableRequest(SetVariableArguments arguments)
        {
            var reference = arguments.VariablesReference;
            /*
            if (reference == -1)
            {
                throw new 
                SendErrorResponse(response, 3009, "variables: property 'variablesReference' is missing", null, false, true);
                return;
            }
            */

            var value = arguments.Value;
            if (m_VariableHandles.TryGet(reference, out var children))
            {
                if (children != null && children.Length > 0)
                {
                    if (children.Length > MAX_CHILDREN)
                    {
                        children = children.Take(MAX_CHILDREN).ToArray();
                    }

                    foreach (var v in children)
                    {
                        if (v.IsError)
                            continue;
                        v.WaitHandle.WaitOne();
                        var variable = CreateVariable(v);
                        if (variable.Name == arguments.Name)
                        {
                            v.Value = value;
                            return new SetVariableResponse(value) {
                                Type = variable.Type,
                                VariablesReference = variable.VariablesReference,
                            };
                        }
                    }
                }
            }

            throw new ProtocolException($"Variable not found: {arguments.Name} ({arguments.VariablesReference})");
        }

        protected override SetExceptionBreakpointsResponse HandleSetExceptionBreakpointsRequest(SetExceptionBreakpointsArguments arguments)
        {
            var exceptionOptions = arguments.ExceptionOptions;
            if (exceptionOptions == null)
            {
                throw new ProtocolException("exceptionOptions is null");
            }

            // clear all existig catchpoints
            foreach (var cp in m_Catchpoints)
            {
                this.m_Session.Breakpoints.Remove(cp);
            }

            this.m_Catchpoints.Clear();

            foreach (var exception in exceptionOptions)
            {
                string exName = null;
                exName = exception.Path?.FirstOrDefault()?.Names?.FirstOrDefault();

                if (exName != null && exception.BreakMode == ExceptionBreakMode.Always)
                {
                    this.m_Catchpoints.Add(this.m_Session.Breakpoints.AddCatchpoint(exName));
                }
            }
            return new SetExceptionBreakpointsResponse();
        }

        protected override SetBreakpointsResponse HandleSetBreakpointsRequest(SetBreakpointsArguments arguments)
        {
            var path = arguments.Source.Path;

            if (!HasMonoExtension(path))
            {
                // we only support breakpoints in files mono can handle
                return new SetBreakpointsResponse();
            }

            var newBreakpoints = arguments.Breakpoints;
            bool sourceModified = arguments.SourceModified ?? false;
            var lines = newBreakpoints.Select(bp => bp.Line);

            Dictionary<int, SdbBreakpoint> dictionary = null;
            if (m_Breakpoints.ContainsKey(path))
            {
                dictionary = m_Breakpoints[path];
                var keys = new int[dictionary.Keys.Count];
                dictionary.Keys.CopyTo(keys, 0);
                foreach (var line in keys)
                {
                    if (!lines.Contains(line) || sourceModified)
                    {
                        var breakpoint = dictionary[line];
                        m_Session.Breakpoints.Remove(breakpoint);
                        dictionary.Remove(line);
                    }
                }
            }
            else
            {
                dictionary = new Dictionary<int, SdbBreakpoint>();
                m_Breakpoints[path] = dictionary;
            }

            var responseBreakpoints = new List<Breakpoint>();
            foreach (var breakpoint in newBreakpoints)
            {
                if (!dictionary.ContainsKey(breakpoint.Line))
                {
                    try
                    {
                        var bp = m_Session.Breakpoints.Add(path, breakpoint.Line);
                        bp.ConditionExpression = breakpoint.Condition;
                        if (!string.IsNullOrEmpty(breakpoint.LogMessage))
                        {
                            bp.HitAction = HitAction.PrintExpression;
                            bp.TraceExpression = breakpoint.LogMessage;
                        }
                        dictionary[breakpoint.Line] = bp;
                        responseBreakpoints.Add(new Breakpoint(true) {
                            Line = breakpoint.Line,
                            Column = breakpoint.Column,
                            //LogMessage = breakpoint.LogMessage,
                        });
                    }
                    catch (Exception e)
                    {
                        // TODO: Why does the old version terminate the request but also add to response breakpoints?
                        //Log.Write(e.StackTrace);
                        //SendErrorResponse(response, 3011, "setBreakpoints: " + e.Message, null, false, true);
                        this.ConsoleLog($"Error setting breakpoint: {e}");
                        //responseBreakpoints.Add(new VSCodeDebug.Breakpoint(false, breakpoint.line, breakpoint.column, e.Message));
                        responseBreakpoints.Add(new Breakpoint(false) {
                            Line = breakpoint.Line,
                            Column = breakpoint.Column,
                            Message = e.Message,
                        });
                    }
                }
                else
                {
                    dictionary[breakpoint.Line].ConditionExpression = breakpoint.Condition;
                    responseBreakpoints.Add(new Breakpoint(true) {
                        Line = breakpoint.Line,
                        Column = breakpoint.Column,
                        //Message = breakpoint.LogMessage,
                    });
                }
            }

            return new SetBreakpointsResponse(responseBreakpoints);
        }

        protected override StackTraceResponse HandleStackTraceRequest(StackTraceArguments arguments)
        {
            var maxLevels = arguments.Levels ?? 0;
            int startFrame = arguments.StartFrame ?? 0;
            int threadReference = arguments.ThreadId;

            WaitForSuspend();

            ThreadInfo thread = DebuggerActiveThread();
            if (thread.Id != threadReference)
            {
                this.ConsoleLog($"Unexpected stack trace thread request: want {threadReference}, but {thread.Id} is active");
                thread = FindThread(threadReference);
                if (thread != null)
                {
                    thread.SetActive();
                }
            }

            var stackFrames = new List<StackFrame>();
            var totalFrames = 0;

            var bt = thread.Backtrace;
            if (bt != null && bt.FrameCount >= 0)
            {
                totalFrames = bt.FrameCount;

                for (var i = startFrame; i < Math.Min(totalFrames, startFrame + maxLevels); i++)
                {
                    var frame = bt.GetFrame(i);

                    string path = frame.SourceLocation.FileName;

                    StackFrame.PresentationHintValue? hint = null;
                    Source source = null;
                    if (!string.IsNullOrEmpty(path))
                    {
                        string sourceName = Path.GetFileName(path);
                        if (!string.IsNullOrEmpty(sourceName))
                        {
                            if (File.Exists(path))
                            {
                                hint = StackFrame.PresentationHintValue.Normal;
                                source = new Source() {
                                    Name = sourceName,
                                    Path = this.ConvertDebuggerPathToClient(path),
                                };
                            }
                            else
                            {
                                source = new Source() {
                                    SourceReference = 1000,
                                    PresentationHint = Source.PresentationHintValue.Deemphasize,
                                };
                            }
                        }
                    }

                    stackFrames.Add(new StackFrame(
                        this.m_FrameHandles.Create(frame),
                        frame.SourceLocation.MethodName,
                        frame.SourceLocation.Line,
                        frame.SourceLocation.Column) {
                            PresentationHint = hint,
                            Source = source,
                    });
                }
            }

            return new StackTraceResponse(stackFrames) {
                TotalFrames = (maxLevels > 0) ? totalFrames : (int?)null,
            };
        }

        ThreadInfo DebuggerActiveThread()
        {
            lock (m_Lock)
            {
                return m_Session?.ActiveThread;
            }
        }

        /*
        public override void Source(Response response, dynamic arguments)
        {
            SendErrorResponse(response, 1020, "No source available");
        }
        */

        protected override ScopesResponse HandleScopesRequest(ScopesArguments arguments)
        {
            var frame = m_FrameHandles.Get(arguments.FrameId, null);

            var scopes = new List<Scope>();

            if (frame.Index == 0 && m_Exception != null)
            {
                scopes.Add(new Scope("Exception", m_VariableHandles.Create(new[] { m_Exception }), false));
            }

            var locals = new[] { frame.GetThisReference() }.Concat(frame.GetParameters()).Concat(frame.GetLocalVariables()).Where(x => x != null).ToArray();
            if (locals.Length > 0)
            {
                scopes.Add(new Scope("Local", m_VariableHandles.Create(locals), false));
            }

            return new ScopesResponse(scopes);
        }

        protected override VariablesResponse HandleVariablesRequest(VariablesArguments arguments)
        {
            int reference = arguments.VariablesReference;
            /*
            if (reference == -1)
            {
                SendErrorResponse(response, 3009, "variables: property 'variablesReference' is missing", null, false, true);
                return;
            }
            */

            WaitForSuspend();
            var variables = new List<Variable>();

            // TODO: implement ranged query

            if (m_VariableHandles.TryGet(reference, out var children))
            {
                if (children != null && children.Length > 0)
                {
                    if (children.Length > MAX_CHILDREN)
                    {
                        children = children.Take(MAX_CHILDREN).ToArray();
                    }

                    if (children.Length < 20)
                    {
                        // Wait for all values at once.
                        WaitHandle.WaitAll(children.Select(x => x.WaitHandle).ToArray());
                        variables.AddRange(from v in children where !v.IsError select CreateVariable(v));
                    }
                    else
                    {
                        foreach (var v in children)
                        {
                            if (v.IsError)
                                continue;
                            v.WaitHandle.WaitOne();
                            variables.Add(CreateVariable(v));
                        }
                    }
                }
            }

            return new VariablesResponse(variables);
        }

        protected override ThreadsResponse HandleThreadsRequest(ThreadsArguments arguments)
        {
            var threads = new List<DapThread>();
            var process = m_ActiveProcess;
            if (process != null)
            {
                Dictionary<int, DapThread> d;
                lock (m_SeenThreads)
                {
                    d = new Dictionary<int, DapThread>(m_SeenThreads);
                }

                foreach (var t in process.GetThreads())
                {
                    int tid = (int)t.Id;
                    d[tid] = new DapThread(tid, t.Name);
                }

                threads = d.Values.ToList();
            }

            return new ThreadsResponse(threads);
        }

        protected override EvaluateResponse HandleEvaluateRequest(EvaluateArguments arguments)
        {
            //SendErrorResponse(response, 3014, "Evaluate request failed ({_reason}).", new { _reason = error });
            ProtocolException evaluationError(string error) {
                return new ProtocolException("eval", new Message(3014, "Evaluate request failed ({_reason}).") {
                    Variables = new Dictionary<string, object>() { { "_reason", error }},
                });
            };

            var expression = arguments.Expression;
            var frameId = arguments.FrameId ?? 0;

            if (expression == null)
            {
                throw evaluationError("expression missing");
            }

            var frame = m_FrameHandles.Get(frameId, null);
            if (frame == null)
            {
                throw evaluationError("no active stackframe");
            }

            if (!frame.ValidateExpression(expression))
            {
                throw evaluationError("invalid expression");
            }

            var evaluationOptions = m_DebuggerSessionOptions.EvaluationOptions.Clone();
            evaluationOptions.EllipsizeStrings = false;
            evaluationOptions.AllowMethodEvaluation = true;
            var val = frame.GetExpressionValue(expression, evaluationOptions);
            val.WaitHandle.WaitOne();

            var flags = val.Flags;
            if (flags.HasFlag(ObjectValueFlags.Error) || flags.HasFlag(ObjectValueFlags.NotSupported))
            {
                string error = val.DisplayValue;
                if (error.IndexOf("reference not available in the current evaluation context") > 0)
                {
                    error = "not available";
                }

                throw evaluationError(error);
            }

            if (flags.HasFlag(ObjectValueFlags.Unknown))
            {
                throw evaluationError("invalid expression");
            }

            if (flags.HasFlag(ObjectValueFlags.Object) && flags.HasFlag(ObjectValueFlags.Namespace))
            {
                throw evaluationError("not available");
            }

            int handle = 0;
            if (val.HasChildren)
            {
                handle = m_VariableHandles.Create(val.GetAllChildren());
            }

            return new EvaluateResponse(val.DisplayValue, handle);
        }

        //---- private ------------------------------------------
        void SetExceptionBreakpoints(dynamic exceptionOptions)
        {
            //Log.Write($"UnityDebug: SetExceptionBreakpoints: {exceptionOptions}");
            if (exceptionOptions == null)
            {
                return;
            }

            // clear all existig catchpoints
            foreach (var cp in m_Catchpoints)
            {
                m_Session.Breakpoints.Remove(cp);
            }

            m_Catchpoints.Clear();

            var exceptions = exceptionOptions.ToObject<dynamic[]>();
            for (var i = 0; i < exceptions.Length; i++)
            {
                var exception = exceptions[i];

                string exName = null;
                string exBreakMode = exception.breakMode;

                if (exception.path != null)
                {
                    var paths = exception.path.ToObject<dynamic[]>();
                    var path = paths[0];
                    if (path.names != null)
                    {
                        var names = path.names.ToObject<dynamic[]>();
                        if (names.Length > 0)
                        {
                            exName = names[0];
                        }
                    }
                }

                if (exName != null && exBreakMode == "always")
                {
                    m_Catchpoints.Add(m_Session.Breakpoints.AddCatchpoint(exName));
                }
            }
        }

        private void ConsoleLog(string message)
        {
            this.Protocol.SendEvent(new OutputEvent(message + "\n") { Category = OutputEvent.CategoryValue.Console });
        }

        ThreadInfo FindThread(int threadReference)
        {
            if (m_ActiveProcess != null)
            {
                foreach (var t in m_ActiveProcess.GetThreads())
                {
                    if (t.Id == threadReference)
                    {
                        return t;
                    }
                }
            }

            return null;
        }

        void Stopped()
        {
            m_Exception = null;
            m_VariableHandles.Reset();
            m_FrameHandles.Reset();
        }

        Variable CreateVariable(ObjectValue v)
        {
            var dv = v.DisplayValue;
            if (dv.Length > 1 && dv[0] == '{' && dv[dv.Length - 1] == '}')
            {
                dv = dv.Substring(1, dv.Length - 2);
            }

            return new Variable(v.Name, dv, v.HasChildren ? this.m_VariableHandles.Create(v.GetAllChildren()) : 0) {
                Type = v.TypeName,
            };
        }

        Backtrace DebuggerActiveBacktrace()
        {
            var thr = DebuggerActiveThread();
            return thr == null ? null : thr.Backtrace;
        }

        ExceptionInfo DebuggerActiveException()
        {
            var bt = DebuggerActiveBacktrace();
            return bt?.GetFrame(0).GetException();
        }

        bool HasMonoExtension(string path)
        {
            return MONO_EXTENSIONS.Any(path.EndsWith);
        }

        void DebuggerKill()
        {
            lock (m_Lock)
            {
                if (m_Session != null)
                {
                    m_DebuggeeExecuting = true;

                    if (!m_Session.HasExited)
                        m_Session.Exit();

                    m_Session.Dispose();
                    m_Session = null;
                }
            }
        }

        void WaitForSuspend()
        {
            if (!m_DebuggeeExecuting) return;

            m_ResumeEvent.WaitOne();
            m_DebuggeeExecuting = false;
        }

        protected string ConvertDebuggerPathToClient(string path)
            => this.PathFormat == InitializeArguments.PathFormatValue.Uri
                ? new Uri(path).AbsolutePath
                : path;
    }
}
