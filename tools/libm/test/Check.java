// Check.java - compare the Java glibc ports (and Math.fma) bit for bit with system-libm vectors (mkvectors.c,
// mkedge.c). Written by Claude (Anthropic).
package swmm5;

import java.io.*;
import java.nio.*;
import java.nio.file.*;

public class Check {
  public static void main(String[] a) throws IOException {
    ByteBuffer b = ByteBuffer.wrap(Files.readAllBytes(Paths.get(a[0]))).order(ByteOrder.LITTLE_ENDIAN);
    java.util.Set<String> only = a.length > 1 ? new java.util.HashSet<>(java.util.Arrays.asList(a[1].split(","))) : null;
    while (b.hasRemaining()) {
      StringBuilder sb = new StringBuilder();
      byte c;
      while ((c = b.get()) != 0) sb.append((char) c);
      String name = sb.toString();
      int n = b.getInt();
      int na = name.equals("pow") ? 2 : name.equals("fma") ? 3 : 1;
      if (only != null && !only.contains(name)) { b.position(b.position() + n * 8 * (na + 1)); continue; }
      long bad = 0, nanSign = 0; int shown = 0;
      long t0 = System.nanoTime();
      for (int i = 0; i < n; i++) {
        double x = b.getDouble(), y = na > 1 ? b.getDouble() : 0, z = na > 2 ? b.getDouble() : 0, want = b.getDouble();
        double got;
        switch (name) {
          case "exp": got = Glibm.exp(x); break;
          case "log": got = Glibm.log(x); break;
          case "log10": got = Glibm.log10(x); break;
          case "pow": got = Glibm.pow(x, y); break;
          case "sin": got = Glibm.sin(x); break;
          case "cos": got = Glibm.cos(x); break;
          case "tan": got = Glibm.tan(x); break;
          case "asin": got = Glibm.asin(x); break;
          case "acos": got = Glibm.acos(x); break;
          case "atan": got = Glibm.atan(x); break;
          default: got = Math.fma(x, y, z);
        }
        long gb = Double.doubleToRawLongBits(got), wb = Double.doubleToRawLongBits(want);
        if (Double.isNaN(got) && Double.isNaN(want)) { if ((gb >>> 63) != (wb >>> 63)) nanSign++; continue; }
        if (gb != wb) {
          bad++;
          if (shown++ < 4) System.out.println("  " + name + "(" + x + (na > 1 ? ", " + y : "") + (na > 2 ? ", " + z : "") + ") = " + got + ", libm " + want);
        }
      }
      System.out.printf("%-6s %d of %d differ, %d NaN sign   (%.3f us/call)%n", name, bad, n, nanSign, (System.nanoTime() - t0) / 1e3 / n);
    }
  }
}
