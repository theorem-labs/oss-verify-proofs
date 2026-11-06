(* Guard for the ASan (lib/A) and ASan+UBSan (lib/Y) proofs against the plain image's instances. Reusable/YI5b.v,
   Reusable/YI5c.v, ZTraceSpec.v and U/ZTraceSpec.v declare #[global] instances of the plain classes:
   src0_sink_head : YI16.sink_head (sk_ofl_head = 0x51920), src0_sink : YI14.sink_syms (sk_ofl_lock = 0x51918),
   src0_sink_laws : YI14.sink_laws and the two checksum_shape : YO09.lib_shape (U/Reusable/YO09.v re-exports the plain
   YO09, so the ubsan copy's checksum_shape is an instance of the plain class too). In a context that loads them, an
   ASan-side argument of one of these classes that is left to instance search gets the plain value. Every lib/A and
   lib/Y file that can load them Requires this file: the walk layers through A/Prog/DiscoPa.v and Reusable/YC4a.v, the
   core through Reusable/DiscoShape.v, and A/DiscoAsanTop.v and A/HaltsSpecD.v directly. This file Requires the four
   modules itself, so the hints are removed in every context that loads it, in any Require order. A plain-side proof in
   such a context gives the plain instance explicitly. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require ZTraceSpec.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require ZTraceSpec.
#[global] Remove Hints lib.Reusable.YI5b.src0_sink_head lib.Reusable.YI5c.src0_sink lib.Reusable.YI5c.src0_sink_laws
  lib.ZTraceSpec.checksum_shape lib.U.ZTraceSpec.checksum_shape : typeclass_instances.
