(* reac-pw/fuzz_link, image A (fuzz_link.asan, pin 059dae63e07c): where link's memory FILE block lies, for the GXA seam
   of musl vfprintf on it (LinkVfSeam.v).

   The FILE is one live block of the ASan allocator of request AMF_BLOCK = 1304 (fmemopen 0x96a1c +0x94..+0x98,
   AMemFileSink.v). AMemFile.v amf_block_facts gives its presence, ownership, shadow and hull, and in_app f 1304,
   whose low arm does not place it. This file adds the one missing fact, amf_block_high: the block lies in high
   application memory. A live block is a chunk of the allocator ledger (YG0s.In_ablocks); its request 1304 is a
   primary size (from_primary 1304 = true), so the chunk is a primary chunk (YG0s.chunk_facts, the PPrim arm of
   cfacts), at region_base + x with x >= 0, and every primary region lies at or above kHighMemBeg
   (YG0s.region_in_prim). The user pointer is the chunk base plus its redzone (16 <= rz), so it is above too.

   amf_block_seam collects what the seam asks of the block: the block high and below the stack's floor, each byte
   present and not the runtime's, and the buffer [f + 280, f + 1304) application memory with its band bound, its
   shadow addressable and its hull visible. *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK04 YK0i YK0s YK14 YK18 YP09 YG0n YG00 YG0a YG01 YG0f YG0v YG0d YA0n YM05 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0s YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require FMgxaSeamReady.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* the FILE block is a primary chunk, so it lies at or above kHighMemBeg *)
Lemma amf_block_high : forall ly S (W : world segs) mem md f,
  AR segs B ly S W mem md -> In (f, AMF_BLOCK) (ablocks B ly S) -> kHighMemBeg <= f.
Proof.
  intros ly S W mem md f HAR Hin.
  destruct (proj1 (YG0s.In_ablocks B ly S f AMF_BLOCK) Hin) as (k & Hk & _ & Hu & Hr).
  pose proof (proj1 HAR) as M. pose proof (am_layout _ _ _ _ M) as LO.
  pose proof (YG0s.chunk_facts B ly S _ k M Hk) as CF. unfold YG0s.cfacts in CF.
  destruct CF as (_ & _ & _ & Hsp & Hrz & _ & _ & _ & HB).
  destruct (ck_beg k) as [|off|r o|c p]; cbv beta iota zeta in HB; try contradiction.
  - destruct HB as (Hc & _ & _ & _ & Hbase & Hx & _).
    pose proof (YG0s.region_in_prim ly (prim_class off) LO ltac:(lia)) as (_ & _ & _ & R4 & _).
    rewrite <- Hu, Hsp, Hbase. lia.
  - destruct HB as (_ & Hfp & _). rewrite Hr in Hfp. vm_compute in Hfp. discriminate Hfp.
Qed.

(* what the seam asks of the block *)
Lemma amf_block_seam : forall ly S (W : world segs) mem md f,
  AR segs B ly S W mem md -> In (f, AMF_BLOCK) (ablocks B ly S) ->
  kHighMemBeg <= f /\ f + AMF_BLOCK <= ASAN_CEIL /\ f mod 16 = 0 /\
  (forall a, f <= a < f + AMF_BLOCK -> apresent (w_H W) mem a /\ ~ aowned B ly S a) /\
  shadow_hull_vis (aview segs (w_H W) mem) (f + AMF_BUF) AMF_BUFSIZ /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (f + AMF_BUF) AMF_BUFSIZ /\
  amem_range (f + AMF_BUF) AMF_BUFSIZ /\ amem_range (f + AMF_BUF) (AMF_BUFSIZ + 8) /\
  ly_stk_lo ly >= ASAN_CEIL.
Proof.
  intros ly S W mem md f HAR Hin.
  pose proof (amf_block_high ly S W mem md f HAR Hin) as Hhi.
  destruct (amf_block_facts segs B LAWS ly S W mem md f HAR Hin) as (H16 & _ & Hceil & _ & Hby & _ & Hhull).
  pose proof (lo_stk_ceil ly (am_layout _ _ _ _ (proj1 HAR))) as SC.
  pose proof ASAN_CEIL_range as [CR _].
  unfold ASAN_CEIL in CR, SC |- *. unfold AMF_BLOCK, AMF_BUF, AMF_BUFSIZ in *.
  split; [exact Hhi|]. split; [exact Hceil|]. split; [exact H16|].
  split; [intros a Ha; destruct (Hby a Ha) as (Hp & Ho & _); split; assumption|].
  split; [exact (FMgxaSeamReady.hull_sub _ f 1304 (f + 280) 1024 Hhull ltac:(lia) ltac:(lia) ltac:(lia))|].
  assert (Hr : req_size 1304 = 1304) by reflexivity.
  split; [exact (YCbq.range_addressable_of_block segs B LAWS ly S W mem md f 1304 (f + 280) 1024 HAR Hin
                   ltac:(lia) ltac:(rewrite Hr; lia))|].
  unfold amem_range, kHighMemBeg, kHighMemEnd in *.
  split; [right; lia|]. split; [right; lia|]. lia.
Qed.

End b.
