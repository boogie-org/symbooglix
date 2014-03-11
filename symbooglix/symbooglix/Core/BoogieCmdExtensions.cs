using Microsoft.Boogie;

namespace symbooglix
{	
	// Although I have access to boogie source code I doubt this could be upstreamed
	// so we'll use extension methods for now
	public static class BoogieCmdExtensions
	{
		public static void visitCmd<T>(this T cmd, IExecutorHandler handler, Executor e) where T: Absy
		{
			// use of "dynamic" might hinder performance. If a problem then manually implement the visitCmd extension methods by hand
			handler.handle(cmd as dynamic, e);
		}
	}
}
