(* The instance of LLVMFuzzerTestOneInput's image-A walk: link's image (LinkImgInst.v `PI_link`), link's
   asyms (lib/A/AD2l.v `PcapB`), link's sink head and memory FILE (lib/A/AMemFile.v `link_asink_head`,
   `link_amf`), and the meter the ASan driver's closing passes (`YCbp.ameter_triv` with
   XM_LIB = XN_LIB = fun _ => 0, staged AD2o.v:53). It discharges every hypothesis of
   lib/A/Prog/LLVMFuzzerTestOneInput.v's Section `top` but LF_WHOLE, so that the walk's remaining obligation is
   exactly the six phase lanes' lemmas.

   THE ALLOCATOR-TRACE CONTEXTS. `LF_CTX` is the list of frame-chain contexts the call's allocating callees
   take (`In (raZ regs :: spine ch) CTX` in text_of / text_buf / mark_quietly's Pre) and over which the
   allocator rules' trace premises are stated. At a callee's entry sp is this call's realigned stack pointer
   and s0 is this call's s0, so the chain is
   `(lf_sp1 cx, <the site's return address>, spZ (c_regs cx)) :: lf_chain cx` and its spine is the site's
   return address followed by `spine (lf_chain cx)`, which is `[RA_LLVMF]` when this call's frame record is on
   the chain and `[]` when it is not (ACejSites.v:48-55: the record's next pointer is target_run's s0, an
   integer, so the chain ends there). `LF_CTX_link` is therefore the two rows of every site of
   `LF_ALLOC_SITES`, which is exactly the shape of ACej.v's CTX_text_of / CTX_text_buf / CTX_mark_quietly and
   of the rows ACejSites.v's llvmf_site_in / text_buf_site_in cover.

   Proves no function (kind: instance of LLVMFuzzerTestOneInput's walk). *)
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.Reusable Require Import
YK11 YK0s YK0o YI16 YM05 YC5d YCbp YG00 YG0f YG0n YG0d YCbq YG01 YGwildCount.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import PaTable PaSym PaRun LinkSyms LinkList LinkAddr LinkPa.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A Require Import AB1v AF0m AD2l AMemFile AMemFileSink.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import link_aaddr link_amem.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LinkEntry LinkEntryA.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInputDefs LinkImgInst.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Prog Require Import LLVMFuzzerTestOneInput.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* the two rows of each allocating site: with and without this call's own frame record on the chain *)
Definition LF_CTX_link : list (list Z) :=
  map (fun s => [link_text + s]) LF_ALLOC_SITES ++
  map (fun s => [link_text + s; RA_LLVMF]) LF_ALLOC_SITES.

Lemma LF_CTX_link_rows : length LF_CTX_link = 32%nat.
Proof. vm_compute. reflexivity. Qed.

Section inst. Context {rc : YM05.RunCeil}.

#[local] Notation PIl := (@PI_link rc).

(* B's owned statics are the start-up's (AD2l.v), which is what G_HARNESS_gx_ok asks. *)
Lemma inst_own : as_owned_static PcapB = Tfib_owned_static.
Proof. reflexivity. Qed.

(* The trace conjunct of lf_base at this LF_CTX: the chain in closed form has spine [] or [RA_LLVMF], and
   both rows of every allocating site are in the list. *)
Lemma inst_ctx : forall (cx : @lcx rc PIl) (regsT : bvmap 5 word),
  raZ (c_regs cx) = RA_LLVMF ->
  In (raZ regsT - @pa_val rc link_listing PIl A_TEXT) LF_ALLOC_SITES ->
  In (raZ regsT :: spine (lf_chain cx)) LF_CTX_link.
Proof.
  intros cx regsT Hra Hs.
  assert (Hval : @pa_val rc link_listing PIl A_TEXT = link_text) by reflexivity.
  rewrite Hval in Hs.
  assert (Hr : raZ regsT = link_text + (raZ regsT - link_text)) by lia.
  unfold lf_chain, LF_CTX_link.
  destruct (spZ (c_regs cx) + 16 <? ly_top (c_ly cx)).
  - cbn [spine map fst snd]. rewrite Hra.
    apply in_or_app. right.
    rewrite Hr at 1.
    apply in_map_iff. exists (raZ regsT - link_text). split; [reflexivity | exact Hs].
  - cbn [spine map]. apply in_or_app. left.
    rewrite Hr at 1.
    apply in_map_iff. exists (raZ regsT - link_text). split; [reflexivity | exact Hs].
Qed.

(* The driver's meter: every charge is 0 and every budget holds (YCbp.v ameter_triv). *)
Lemma inst_mo : 0 <= 0 /\ 0 <= 0 /\ 0 <= (0 : Z).
Proof. repeat split; lia. Qed.
Lemma inst_bud : forall n : Z, 0 + 48 * 0 + 0 <= (fun _ : Z => 0) n.
Proof. intros n. cbn. lia. Qed.
Lemma inst_xmn : forall n : Z, (fun _ : Z => 0) n <= (fun _ : Z => 0) n.
Proof. intros n. cbn. lia. Qed.

(* The walk at the instance, as the six phase lanes prove it through lf_whole. *)
Definition LF_WHOLE_A : Prop := forall fx : YK11.FPState,
  @lf_start fx rc link_asink_head PIl PcapB ameter_triv (fun _ : Z => 0) (fun _ : Z => 0) link_amf LA_NUL
    LF_CTX_link 0 0 0
    (@lf_post rc link_asink_head PIl PcapB ameter_triv (fun _ : Z => 0) link_amf LA_NUL).

(* THE ASan BUILD'S ENTRY CONTRACT of link, at the lib/A instance and at the driver's meter. *)
Theorem LLVMFuzzerTestOneInput_aproof_A : LF_WHOLE_A ->
  @tfib_lib_contract_xf_all_A rc link_asink_head PcapB ameter_triv (fun _ : Z => 0) (fun _ : Z => 0).
Proof.
  intros HW.
  exact (@LLVMFuzzerTestOneInput_aproof rc link_asink_head PcapB ameter_triv
           (fun _ : Z => 0) (fun _ : Z => 0) LF_CTX_link 0 0 0
           HW inst_own inst_ctx inst_mo inst_bud inst_xmn (@ameter_triv_laws) (@ameter_triv_fs_laws)).
Qed.

End inst.

About LLVMFuzzerTestOneInput_aproof_A.
Print Assumptions LLVMFuzzerTestOneInput_aproof_A.
