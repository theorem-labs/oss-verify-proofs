(* on_data_segs: the contract of on_data at its entry with trans_tf_off_g TF (lib/A/Prog/on_data_seg_cut.v
   od_top_at), from the nine pieces of the walk at the cuts of on_data_seg_cut.v: head (on_data_seg_head.v), the
   call of send_control (on_data_seg_sc.v), acks / dup / set (on_data_seg_acks.v, _dup.v, _set.v), the leaf call
   (on_data_seg_ka.v), the notice path (on_data_seg_ntc.v), the call of notice (on_data_seg_ncall.v) and the release
   (on_data_seg_rel.v). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_data_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
on_data_seg_head on_data_seg_sc on_data_seg_acks on_data_seg_dup on_data_seg_set on_data_seg_ka on_data_seg_ntc
on_data_seg_ncall on_data_seg_rel.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

Theorem od_top : forall (fx : YK11.FPState) (rc : YM05.RunCeil) B MT, @od_top_at fx rc B MT.
Proof.
intros fx rc B MT.
exact (@od_top_of fx rc B MT (od_head fx rc B MT) (od_sc fx rc B MT) (od_acks fx rc B MT) (od_dup fx rc B MT)
  (od_set fx rc B MT) (od_ka fx rc B MT) (od_ntc fx rc B MT) (od_ncall fx rc B MT) (od_rel fx rc B MT)).
Qed.
