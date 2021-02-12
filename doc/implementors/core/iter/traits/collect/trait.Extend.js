(function() {var implementors = {};
implementors["bytes"] = [{"text":"impl Extend&lt;u8&gt; for Bytes","synthetic":false,"types":[]},{"text":"impl&lt;'a&gt; Extend&lt;&amp;'a u8&gt; for Bytes","synthetic":false,"types":[]},{"text":"impl Extend&lt;u8&gt; for BytesMut","synthetic":false,"types":[]},{"text":"impl&lt;'a&gt; Extend&lt;&amp;'a u8&gt; for BytesMut","synthetic":false,"types":[]}];
implementors["csv"] = [{"text":"impl&lt;T:&nbsp;AsRef&lt;[u8]&gt;&gt; Extend&lt;T&gt; for ByteRecord","synthetic":false,"types":[]},{"text":"impl&lt;T:&nbsp;AsRef&lt;str&gt;&gt; Extend&lt;T&gt; for StringRecord","synthetic":false,"types":[]}];
implementors["either"] = [{"text":"impl&lt;L, R, A&gt; Extend&lt;A&gt; for Either&lt;L, R&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;L: Extend&lt;A&gt;,<br>&nbsp;&nbsp;&nbsp;&nbsp;R: Extend&lt;A&gt;,&nbsp;</span>","synthetic":false,"types":[]}];
implementors["futures_util"] = [{"text":"impl&lt;Fut:&nbsp;Future&gt; Extend&lt;Fut&gt; for FuturesOrdered&lt;Fut&gt;","synthetic":false,"types":[]},{"text":"impl&lt;Fut&gt; Extend&lt;Fut&gt; for FuturesUnordered&lt;Fut&gt;","synthetic":false,"types":[]},{"text":"impl&lt;St:&nbsp;Stream + Unpin&gt; Extend&lt;St&gt; for SelectAll&lt;St&gt;","synthetic":false,"types":[]}];
implementors["git2"] = [{"text":"impl Extend&lt;Sort&gt; for Sort","synthetic":false,"types":[]},{"text":"impl Extend&lt;CredentialType&gt; for CredentialType","synthetic":false,"types":[]},{"text":"impl Extend&lt;IndexEntryFlag&gt; for IndexEntryFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;IndexEntryExtendedFlag&gt; for IndexEntryExtendedFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;IndexAddOption&gt; for IndexAddOption","synthetic":false,"types":[]},{"text":"impl Extend&lt;RepositoryOpenFlags&gt; for RepositoryOpenFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;RevparseMode&gt; for RevparseMode","synthetic":false,"types":[]},{"text":"impl Extend&lt;MergeAnalysis&gt; for MergeAnalysis","synthetic":false,"types":[]},{"text":"impl Extend&lt;MergePreference&gt; for MergePreference","synthetic":false,"types":[]},{"text":"impl Extend&lt;Status&gt; for Status","synthetic":false,"types":[]},{"text":"impl Extend&lt;RepositoryInitMode&gt; for RepositoryInitMode","synthetic":false,"types":[]},{"text":"impl Extend&lt;SubmoduleStatus&gt; for SubmoduleStatus","synthetic":false,"types":[]},{"text":"impl Extend&lt;PathspecFlags&gt; for PathspecFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;CheckoutNotificationType&gt; for CheckoutNotificationType","synthetic":false,"types":[]},{"text":"impl Extend&lt;DiffStatsFormat&gt; for DiffStatsFormat","synthetic":false,"types":[]},{"text":"impl Extend&lt;StashApplyFlags&gt; for StashApplyFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;StashFlags&gt; for StashFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;AttrCheckFlags&gt; for AttrCheckFlags","synthetic":false,"types":[]}];
implementors["hashbrown"] = [{"text":"impl&lt;K, V, S&gt; Extend&lt;(K, V)&gt; for HashMap&lt;K, V, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: Eq + Hash,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;'a, K, V, S&gt; Extend&lt;(&amp;'a K, &amp;'a V)&gt; for HashMap&lt;K, V, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: Eq + Hash + Copy,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: Copy,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;T, S&gt; Extend&lt;T&gt; for HashSet&lt;T, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: Eq + Hash,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;'a, T, S&gt; Extend&lt;&amp;'a T&gt; for HashSet&lt;T, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: 'a + Eq + Hash + Copy,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]}];
implementors["http"] = [{"text":"impl&lt;T&gt; Extend&lt;(Option&lt;HeaderName&gt;, T)&gt; for HeaderMap&lt;T&gt;","synthetic":false,"types":[]},{"text":"impl&lt;T&gt; Extend&lt;(HeaderName, T)&gt; for HeaderMap&lt;T&gt;","synthetic":false,"types":[]}];
implementors["im_rc"] = [{"text":"impl&lt;K, V, RK, RV&gt; Extend&lt;(RK, RV)&gt; for OrdMap&lt;K, V&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: Ord + Clone + From&lt;RK&gt;,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: Clone + From&lt;RV&gt;,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;A, R&gt; Extend&lt;R&gt; for OrdSet&lt;A&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: Ord + Clone + From&lt;R&gt;,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;K, V, S, RK, RV&gt; Extend&lt;(RK, RV)&gt; for HashMap&lt;K, V, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: Hash + Eq + Clone + From&lt;RK&gt;,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: Clone + From&lt;RV&gt;,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;A, S, R&gt; Extend&lt;R&gt; for HashSet&lt;A, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: Hash + Eq + Clone + From&lt;R&gt;,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;A:&nbsp;Clone&gt; Extend&lt;A&gt; for Vector&lt;A&gt;","synthetic":false,"types":[]}];
implementors["indexmap"] = [{"text":"impl&lt;K, V, S&gt; Extend&lt;(K, V)&gt; for IndexMap&lt;K, V, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: Hash + Eq,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;'a, K, V, S&gt; Extend&lt;(&amp;'a K, &amp;'a V)&gt; for IndexMap&lt;K, V, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;K: Hash + Eq + Copy,<br>&nbsp;&nbsp;&nbsp;&nbsp;V: Copy,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;T, S&gt; Extend&lt;T&gt; for IndexSet&lt;T, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: Hash + Eq,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;'a, T, S&gt; Extend&lt;&amp;'a T&gt; for IndexSet&lt;T, S&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;T: Hash + Eq + Copy + 'a,<br>&nbsp;&nbsp;&nbsp;&nbsp;S: BuildHasher,&nbsp;</span>","synthetic":false,"types":[]}];
implementors["nix"] = [{"text":"impl Extend&lt;AtFlags&gt; for AtFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;OFlag&gt; for OFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;SealFlag&gt; for SealFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;FdFlag&gt; for FdFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;SpliceFFlags&gt; for SpliceFFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;FallocateFlags&gt; for FallocateFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;ModuleInitFlags&gt; for ModuleInitFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;DeleteModuleFlags&gt; for DeleteModuleFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;MsFlags&gt; for MsFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;MntFlags&gt; for MntFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;MQ_OFlag&gt; for MQ_OFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;FdFlag&gt; for FdFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;InterfaceFlags&gt; for InterfaceFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;PollFlags&gt; for PollFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;CloneFlags&gt; for CloneFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;EpollFlags&gt; for EpollFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;EpollCreateFlags&gt; for EpollCreateFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;EfdFlags&gt; for EfdFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;MemFdCreateFlag&gt; for MemFdCreateFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;ProtFlags&gt; for ProtFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;MapFlags&gt; for MapFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;MsFlags&gt; for MsFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;MlockAllFlags&gt; for MlockAllFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;Options&gt; for Options","synthetic":false,"types":[]},{"text":"impl Extend&lt;QuotaValidFlags&gt; for QuotaValidFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;SaFlags&gt; for SaFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;SfdFlags&gt; for SfdFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;SockFlag&gt; for SockFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;MsgFlags&gt; for MsgFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;SFlag&gt; for SFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;Mode&gt; for Mode","synthetic":false,"types":[]},{"text":"impl Extend&lt;FsFlags&gt; for FsFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;InputFlags&gt; for InputFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;OutputFlags&gt; for OutputFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;ControlFlags&gt; for ControlFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;LocalFlags&gt; for LocalFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;WaitPidFlag&gt; for WaitPidFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;AddWatchFlags&gt; for AddWatchFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;InitFlags&gt; for InitFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;TimerFlags&gt; for TimerFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;TimerSetTimeFlags&gt; for TimerSetTimeFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;AccessFlags&gt; for AccessFlags","synthetic":false,"types":[]}];
implementors["openssl"] = [{"text":"impl Extend&lt;CMSOptions&gt; for CMSOptions","synthetic":false,"types":[]},{"text":"impl Extend&lt;OcspFlag&gt; for OcspFlag","synthetic":false,"types":[]},{"text":"impl Extend&lt;Pkcs7Flags&gt; for Pkcs7Flags","synthetic":false,"types":[]},{"text":"impl Extend&lt;SslOptions&gt; for SslOptions","synthetic":false,"types":[]},{"text":"impl Extend&lt;SslMode&gt; for SslMode","synthetic":false,"types":[]},{"text":"impl Extend&lt;SslVerifyMode&gt; for SslVerifyMode","synthetic":false,"types":[]},{"text":"impl Extend&lt;SslSessionCacheMode&gt; for SslSessionCacheMode","synthetic":false,"types":[]},{"text":"impl Extend&lt;ExtensionContext&gt; for ExtensionContext","synthetic":false,"types":[]},{"text":"impl Extend&lt;ShutdownState&gt; for ShutdownState","synthetic":false,"types":[]},{"text":"impl Extend&lt;X509CheckFlags&gt; for X509CheckFlags","synthetic":false,"types":[]},{"text":"impl Extend&lt;X509VerifyFlags&gt; for X509VerifyFlags","synthetic":false,"types":[]}];
implementors["proc_macro2"] = [{"text":"impl Extend&lt;TokenTree&gt; for TokenStream","synthetic":false,"types":[]},{"text":"impl Extend&lt;TokenStream&gt; for TokenStream","synthetic":false,"types":[]}];
implementors["serde_json"] = [{"text":"impl Extend&lt;(String, Value)&gt; for Map&lt;String, Value&gt;","synthetic":false,"types":[]}];
implementors["sized_chunks"] = [{"text":"impl&lt;A, T&gt; Extend&lt;A&gt; for InlineArray&lt;A, T&gt;","synthetic":false,"types":[]},{"text":"impl&lt;'a, A, T&gt; Extend&lt;&amp;'a A&gt; for InlineArray&lt;A, T&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: 'a + Copy,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;A, N:&nbsp;ChunkLength&lt;A&gt;&gt; Extend&lt;A&gt; for RingBuffer&lt;A, N&gt;","synthetic":false,"types":[]},{"text":"impl&lt;'a, A:&nbsp;Clone + 'a, N:&nbsp;ChunkLength&lt;A&gt;&gt; Extend&lt;&amp;'a A&gt; for RingBuffer&lt;A, N&gt;","synthetic":false,"types":[]},{"text":"impl&lt;A, N&gt; Extend&lt;A&gt; for Chunk&lt;A, N&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;N: ChunkLength&lt;A&gt;,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;'a, A, N&gt; Extend&lt;&amp;'a A&gt; for Chunk&lt;A, N&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;A: 'a + Copy,<br>&nbsp;&nbsp;&nbsp;&nbsp;N: ChunkLength&lt;A&gt;,&nbsp;</span>","synthetic":false,"types":[]}];
implementors["smallvec"] = [{"text":"impl&lt;A:&nbsp;Array&gt; Extend&lt;&lt;A as Array&gt;::Item&gt; for SmallVec&lt;A&gt;","synthetic":false,"types":[]}];
implementors["syn"] = [{"text":"impl&lt;T, P&gt; Extend&lt;T&gt; for Punctuated&lt;T, P&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;P: Default,&nbsp;</span>","synthetic":false,"types":[]},{"text":"impl&lt;T, P&gt; Extend&lt;Pair&lt;T, P&gt;&gt; for Punctuated&lt;T, P&gt;","synthetic":false,"types":[]},{"text":"impl Extend&lt;Error&gt; for Error","synthetic":false,"types":[]}];
implementors["tinyvec"] = [{"text":"impl&lt;A:&nbsp;Array&gt; Extend&lt;&lt;A as Array&gt;::Item&gt; for ArrayVec&lt;A&gt;","synthetic":false,"types":[]},{"text":"impl&lt;'s, T&gt; Extend&lt;T&gt; for SliceVec&lt;'s, T&gt;","synthetic":false,"types":[]},{"text":"impl&lt;A:&nbsp;Array&gt; Extend&lt;&lt;A as Array&gt;::Item&gt; for TinyVec&lt;A&gt;","synthetic":false,"types":[]}];
implementors["toml"] = [{"text":"impl Extend&lt;(String, Value)&gt; for Map&lt;String, Value&gt;","synthetic":false,"types":[]}];
implementors["vec_map"] = [{"text":"impl&lt;V&gt; Extend&lt;(usize, V)&gt; for VecMap&lt;V&gt;","synthetic":false,"types":[]},{"text":"impl&lt;'a, V:&nbsp;Copy&gt; Extend&lt;(usize, &amp;'a V)&gt; for VecMap&lt;V&gt;","synthetic":false,"types":[]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()