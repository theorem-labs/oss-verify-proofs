(* reac-pw/fuzz_link, image A (the asan build, pin 059dae63e07c): the top lemma of fmemopen(g_said, 4096, "w") at its
   wrapper's jump 0x430a8, the contract mark_quietly's walk cites at 0x88410 (LinkFoSpec.v afmemopen_w_spec).

   It composes the three walks:
   - LinkFoWrap.v fo_wrap_ok: the wrapper 0x430a8 -> ___interceptor_fmemopen 0x48024 -> TryAsanInitFromRtl ->
     REAL(fmemopen) 0x96a1c, from the same statement at 0x96a1c;
   - LinkFoMusl.v fo_musl_ok: musl fmemopen's "w" arm with __ofl_add / __ofl_lock / __lock / __ofl_unlock / __unlock,
     from the strchr calls (afm_strchr_lit), the depot-aware malloc rule (LinkMallocDepot.v amalloc04_rule_d: the
     frame's amalloc04_rule and the depot step) and the memset wrapper (aintrin_realizes OSet at 0x52d70);
   - LinkFoStrchr.v fo_strchr_lit: the two strchr calls through the strchr wrapper 0x43054.
   The memset wrapper is the frame's closed lib/A/AE32.v memset_icpt_realizes; AR's laws are the frame's closed
   lib/Reusable/YG0q.v AR_laws_ok. So afmemopen_w_ok's only premises are PcapSyms B and the malloc rule of the
   caller's meter MT; at link's instance (PcapB, the frame's trivial meter, whose depot-aware malloc rule is
   LinkMallocDepotA.v PcapB_AMALLOC4_D) afmemopen_w_ok_pcapb has none. Proves no function (kind: composition). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.reac_pw.fuzz_link.images Require Asan.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK11 YK0s YM05 YI00 YI04 YI16.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YK04 YA0i YA0n YP09.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import YG00 YG0f YG0n YG0d YCbq YC5d YCbp.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD2l AMemFile.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require AE32.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMfDefs LinkFoSpec LinkFoStrchrDef.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require Import LinkMallocDepot LinkMallocDepotA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Rt Require LinkFoStrchr LinkFoMusl LinkFoWrap.
Import ListNotations.
Local Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* the memset wrapper at 0x52d70 (fmemopen +0xbc), from the frame's closed walk *)
Lemma fo_aintr : forall B, PcapSyms B -> aintrin_realizes tfibsegs B OSet 0x52d70.
Proof.
  intros B HT ly S W regs mem md d x n HE H10 H11 H12 Hn Hd Hdn Hdo Ham Hra Hsh _.
  exact (AE32.memset_icpt_realizes B (YG0q.AR_laws_ok tfibsegs B) HT ly S W regs mem md d x n HE H10 H11 H12 Hn Hd Hdn
           Hdo Hra Hsh Ham).
Qed.

(* the top lemma: every asyms record of link's image, every meter whose malloc rule holds, every CTX *)
Theorem afmemopen_w_ok : forall (B : asyms) (MT : ameter_ops) (CTX : list (list Z)),
  PcapSyms B -> amalloc04_rule_d (SK := link_asink_head) tfibsegs B MT ->
  afmemopen_w_spec link_asink_head tfibsegs B link_amf MT CTX LA_W_FMEMOPEN LA_FM_MALLOC_RA 0x10360 0x10380.
Proof.
  intros B MT CTX TB AMR.
  apply (LinkFoWrap.fo_wrap_ok B TB MT CTX).
  exact (LinkFoMusl.fo_musl_ok B MT CTX TB AMR (fo_aintr B TB) (LinkFoStrchr.fo_strchr_lit B TB)).
Qed.

(* at link's instance PcapB with the frame's trivial meter: no premise *)
Theorem afmemopen_w_ok_pcapb : forall CTX : list (list Z),
  afmemopen_w_spec link_asink_head tfibsegs PcapB link_amf ameter_triv CTX LA_W_FMEMOPEN LA_FM_MALLOC_RA 0x10360 0x10380.
Proof.
  intros CTX. exact (afmemopen_w_ok PcapB ameter_triv CTX PcapB_syms (PcapB_AMALLOC4_D (SK := link_asink_head))).
Qed.

(* g_said [0x62fee0, 0x630ee0) is outside the runtime's owned statics (lib/A/AF0m.v Tfib_owned_static) *)
Lemma fo_said_unowned : forall a, 0x62fee0 <= a < 0x630ee0 -> ~ Exists (in_zr a) Tfib_owned_static.
Proof.
  intros a Ha HE. apply Exists_exists in HE as (r & Hin & Hr).
  assert (C : forallb (fun r => (fst r + snd r <=? 0x62fee0) || (0x630ee0 <=? fst r)) Tfib_owned_static = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in C. specialize (C r Hin). unfold in_zr in Hr.
  apply orb_prop in C as [C|C]; apply Z.leb_le in C; lia.
Qed.

(* Every A journal of link's image (the post of afmemopen_w_spec among them) keeps g_said's bytes: they are image
   bytes (the fourth loaded segment, .bss) outside the owned statics, errno (0x631b6c) and the list head (0x652308),
   which is the journal's image clause (lib/Reusable/YCbq.v ajournal). Mode "w" writes none of them. *)
Lemma fo_said_kept :
  forall B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
  PcapSyms B ->
  ajournal (SK := link_asink_head) tfibsegs B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  forall a, amf_buf link_amf <= a < amf_buf link_amf + amf_size link_amf ->
  aview tfibsegs (w_H W') mem' a = aview tfibsegs (w_H W) mem a.
Proof.
  intros B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k TB HJ a Ha.
  pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
  cbn [amf_buf amf_size link_amf] in Ha.
  apply F3.
  - exists Asan.Asan_segment_003. split; [do 3 right; left; reflexivity|]. cbn. lia.
  - rewrite (ts_owned B TB). apply fo_said_unowned. lia.
  - rewrite (ts_errno B TB). unfold TFIB_ERRNO. lia.
  - apply fp_spares_off. unfold AOFL_HEAD, link_asink_head. cbn. lia.
Qed.

End t.

About afmemopen_w_ok.
Print Assumptions afmemopen_w_ok.
About afmemopen_w_ok_pcapb.
Print Assumptions afmemopen_w_ok_pcapb.
Print Assumptions fo_said_kept.
