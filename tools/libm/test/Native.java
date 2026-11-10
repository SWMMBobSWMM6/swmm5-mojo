// Native.java - how often Java's Math.* and StrictMath.* differ from glibc on the test vectors.
// javac Native.java && java Native vectors.bin. Written by Claude (Anthropic).
import java.nio.*; import java.nio.file.*;
public class Native { public static void main(String[] a) throws Exception {
  ByteBuffer b = ByteBuffer.wrap(Files.readAllBytes(Paths.get(a[0]))).order(ByteOrder.LITTLE_ENDIAN);
  while (b.hasRemaining()) { StringBuilder sb = new StringBuilder(); byte c; while ((c = b.get()) != 0) sb.append((char) c);
    String name = sb.toString(); int n = b.getInt(); int na = name.equals("pow") ? 2 : name.equals("fma") ? 3 : 1;
    if (name.equals("fma")) { b.position(b.position() + n * 8 * (na + 1)); continue; }
    long bad = 0, sbad = 0;
    for (int i = 0; i < n; i++) { double x = b.getDouble(), y = na > 1 ? b.getDouble() : 0, w = b.getDouble(); double g, h;
      switch (name) { case "exp": g = Math.exp(x); h = StrictMath.exp(x); break; case "log": g = Math.log(x); h = StrictMath.log(x); break;
        case "log10": g = Math.log10(x); h = StrictMath.log10(x); break; case "pow": g = Math.pow(x, y); h = StrictMath.pow(x, y); break;
        case "sin": g = Math.sin(x); h = StrictMath.sin(x); break; case "cos": g = Math.cos(x); h = StrictMath.cos(x); break;
        case "tan": g = Math.tan(x); h = StrictMath.tan(x); break; case "asin": g = Math.asin(x); h = StrictMath.asin(x); break;
        case "acos": g = Math.acos(x); h = StrictMath.acos(x); break; default: g = Math.atan(x); h = StrictMath.atan(x); }
      if (!(Double.isNaN(g) && Double.isNaN(w)) && Double.doubleToRawLongBits(g) != Double.doubleToRawLongBits(w)) bad++;
      if (!(Double.isNaN(h) && Double.isNaN(w)) && Double.doubleToRawLongBits(h) != Double.doubleToRawLongBits(w)) sbad++; }
    System.out.printf("Java Math.%-6s %d of %d differ from glibc (%.2f%%); StrictMath %d (%.2f%%)%n", name, bad, n, 100.0 * bad / n, sbad, 100.0 * sbad / n); } } }
