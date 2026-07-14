import type { Metadata } from "next";
import "./globals.css";

export const metadata: Metadata = {
  title: "Conformal Covariant Operators — Interactive Project Map",
  description: "Explore the Lean 4 formalization of conformally covariant operators through its interactive project map.",
};

export default function RootLayout({ children }: Readonly<{ children: React.ReactNode }>) {
  return <html lang="zh-CN"><body>{children}</body></html>;
}
