(function() {var implementors = {};
implementors["git2"] = [{"text":"impl BitXor&lt;Sort&gt; for Sort","synthetic":false,"types":[]},{"text":"impl BitXor&lt;CredentialType&gt; for CredentialType","synthetic":false,"types":[]},{"text":"impl BitXor&lt;IndexEntryFlag&gt; for IndexEntryFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;IndexEntryExtendedFlag&gt; for IndexEntryExtendedFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;IndexAddOption&gt; for IndexAddOption","synthetic":false,"types":[]},{"text":"impl BitXor&lt;RepositoryOpenFlags&gt; for RepositoryOpenFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;RevparseMode&gt; for RevparseMode","synthetic":false,"types":[]},{"text":"impl BitXor&lt;MergeAnalysis&gt; for MergeAnalysis","synthetic":false,"types":[]},{"text":"impl BitXor&lt;MergePreference&gt; for MergePreference","synthetic":false,"types":[]},{"text":"impl BitXor&lt;Status&gt; for Status","synthetic":false,"types":[]},{"text":"impl BitXor&lt;RepositoryInitMode&gt; for RepositoryInitMode","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SubmoduleStatus&gt; for SubmoduleStatus","synthetic":false,"types":[]},{"text":"impl BitXor&lt;PathspecFlags&gt; for PathspecFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;CheckoutNotificationType&gt; for CheckoutNotificationType","synthetic":false,"types":[]},{"text":"impl BitXor&lt;DiffStatsFormat&gt; for DiffStatsFormat","synthetic":false,"types":[]},{"text":"impl BitXor&lt;StashApplyFlags&gt; for StashApplyFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;StashFlags&gt; for StashFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;AttrCheckFlags&gt; for AttrCheckFlags","synthetic":false,"types":[]}];
implementors["hashbrown"] = [{"text":"impl&lt;T, S&gt; BitXor&lt;&amp;'_ HashSet&lt;T, S&gt;&gt; for &amp;HashSet&lt;T, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: Eq + Hash + Clone,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher + Default,&nbsp;</span>","synthetic":false,"types":[]}];
implementors["indexmap"] = [{"text":"impl&lt;T, S1, S2&gt; BitXor&lt;&amp;'_ IndexSet&lt;T, S2&gt;&gt; for &amp;IndexSet&lt;T, S1&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: Eq + Hash + Clone,<br>&nbsp;&nbsp;&nbsp;&nbsp;S1: BuildHasher + Default,<br>&nbsp;&nbsp;&nbsp;&nbsp;S2: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]}];
implementors["mio"] = [{"text":"impl BitXor&lt;PollOpt&gt; for PollOpt","synthetic":false,"types":[]},{"text":"impl&lt;T:&nbsp;Into&lt;Ready&gt;&gt; BitXor&lt;T&gt; for Ready","synthetic":false,"types":[]},{"text":"impl BitXor&lt;UnixReady&gt; for UnixReady","synthetic":false,"types":[]}];
implementors["nix"] = [{"text":"impl BitXor&lt;AtFlags&gt; for AtFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;OFlag&gt; for OFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SealFlag&gt; for SealFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;FdFlag&gt; for FdFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SpliceFFlags&gt; for SpliceFFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;FallocateFlags&gt; for FallocateFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;ModuleInitFlags&gt; for ModuleInitFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;DeleteModuleFlags&gt; for DeleteModuleFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;MsFlags&gt; for MsFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;MntFlags&gt; for MntFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;MQ_OFlag&gt; for MQ_OFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;FdFlag&gt; for FdFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;InterfaceFlags&gt; for InterfaceFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;PollFlags&gt; for PollFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;CloneFlags&gt; for CloneFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;EpollFlags&gt; for EpollFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;EpollCreateFlags&gt; for EpollCreateFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;EfdFlags&gt; for EfdFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;MemFdCreateFlag&gt; for MemFdCreateFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;ProtFlags&gt; for ProtFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;MapFlags&gt; for MapFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;MsFlags&gt; for MsFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;MlockAllFlags&gt; for MlockAllFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;Options&gt; for Options","synthetic":false,"types":[]},{"text":"impl BitXor&lt;QuotaValidFlags&gt; for QuotaValidFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SaFlags&gt; for SaFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SfdFlags&gt; for SfdFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SockFlag&gt; for SockFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;MsgFlags&gt; for MsgFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SFlag&gt; for SFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;Mode&gt; for Mode","synthetic":false,"types":[]},{"text":"impl BitXor&lt;FsFlags&gt; for FsFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;InputFlags&gt; for InputFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;OutputFlags&gt; for OutputFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;ControlFlags&gt; for ControlFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;LocalFlags&gt; for LocalFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;WaitPidFlag&gt; for WaitPidFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;AddWatchFlags&gt; for AddWatchFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;InitFlags&gt; for InitFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;AccessFlags&gt; for AccessFlags","synthetic":false,"types":[]}];
implementors["openssl"] = [{"text":"impl BitXor&lt;CMSOptions&gt; for CMSOptions","synthetic":false,"types":[]},{"text":"impl BitXor&lt;OcspFlag&gt; for OcspFlag","synthetic":false,"types":[]},{"text":"impl BitXor&lt;Pkcs7Flags&gt; for Pkcs7Flags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SslOptions&gt; for SslOptions","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SslMode&gt; for SslMode","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SslVerifyMode&gt; for SslVerifyMode","synthetic":false,"types":[]},{"text":"impl BitXor&lt;SslSessionCacheMode&gt; for SslSessionCacheMode","synthetic":false,"types":[]},{"text":"impl BitXor&lt;ExtensionContext&gt; for ExtensionContext","synthetic":false,"types":[]},{"text":"impl BitXor&lt;ShutdownState&gt; for ShutdownState","synthetic":false,"types":[]},{"text":"impl BitXor&lt;X509CheckFlags&gt; for X509CheckFlags","synthetic":false,"types":[]},{"text":"impl BitXor&lt;X509VerifyFlags&gt; for X509VerifyFlags","synthetic":false,"types":[]}];
implementors["typenum"] = [{"text":"impl BitXor&lt;B0&gt; for B0","synthetic":false,"types":[]},{"text":"impl BitXor&lt;B0&gt; for B1","synthetic":false,"types":[]},{"text":"impl BitXor&lt;B1&gt; for B0","synthetic":false,"types":[]},{"text":"impl BitXor&lt;B1&gt; for B1","synthetic":false,"types":[]},{"text":"impl&lt;Ur:&nbsp;Unsigned&gt; BitXor&lt;Ur&gt; for UTerm","synthetic":false,"types":[]},{"text":"impl&lt;Ul:&nbsp;Unsigned, Bl:&nbsp;Bit, Ur:&nbsp;Unsigned&gt; BitXor&lt;Ur&gt; for UInt&lt;Ul, Bl&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;UInt&lt;Ul, Bl&gt;: PrivateXor&lt;Ur&gt;,<br>&nbsp;&nbsp;&nbsp;&nbsp;PrivateXorOut&lt;UInt&lt;Ul, Bl&gt;, Ur&gt;: Trim,&nbsp;</span>","synthetic":false,"types":[]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()