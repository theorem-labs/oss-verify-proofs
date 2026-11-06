(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address measured on the unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, same loaded bytes except .note.gnu.build-id): the harness-level cuts C2
   0x82e60 (the `jal` of malloc(pod), a0 = len + (len == 0) from 0x82e58 .. 0x82e5c) and C3 0x82e64 (`beqz a0` after
   it), and the statement of the malloc(pod) step C2 -> C3, in lib/A/HPgSegM.v's form (hq_at_cut, and the step's
   post as hq_at_C7 states the malloc(first) step's: the call's post and the whole next cut). Statement text only:
   proves no function (kind: segment lemma).

   C2 is what headamp_build_contract's post gives the step (the chaining builds it); C3 is what
   headamp_dup_contract's premises and the later cuts need: the record r the pp block holds (r is
   fst (Model.pod_build rest) of the bytes after the two harness bytes), the pod block's request len = |buf r|, the
   harness bytes' ranges, and rc = the parse's answer on the pod (e_rc is a free quantity of the env until here; no
   cut list of C1 .. C5 reads it). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Open Scope Z_scope.

Definition HQ_C2 : Z := 0x82e60.    (* the `jal` of malloc(pod) *)
Definition HQ_C3 : Z := 0x82e64.    (* `beqz a0` after it *)
Lemma hq_c23_himg : hi_c2 headamp_himg_A = HQ_C2 /\ hi_c3 headamp_himg_A = HQ_C3.
Proof. split; reflexivity. Qed.

(* C2's values do not read XPod, so the env gains the returned block only at C3. *)
Definition hq_env_pod (e : hd_env) (pod : Z) : hd_env :=
  HDEnv (e_S e) (e_R e) (e_F e) (e_pp e) pod (e_out e) (e_first e) (e_len e) (e_cap e) (e_null e) (e_rc e)
        (e_src e) (e_left e).
Lemma hq_env_pod_xv : forall e pod x, x <> XPod -> x <> XProps -> hd_xv (hq_env_pod e pod) x = hd_xv e x.
Proof. intros e pod x H1 H2. destruct x; cbn; try reflexivity; exfalso; auto. Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section c.
Variable segs : list Segment.
Variable B : asyms.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK : Z.

(* The record's data C2 .. C4 carry before the pod block holds the record's buffer (HPgSegM.hq_rec without its
   pod clauses): r well formed, the pod request len = |buf r| and its bounds, the pp block holding r's image, the
   harness bytes' ranges, and rc = the parse's answer on the pod bytes. *)
Definition hq_recP (e : hd_env) (r : Model.pod_rec) (W : world segs) (mem : word -> option byte) : Prop :=
Model.pod_rec_wf r /\ e_len e = Z.of_nat (length (Model.buf r)) /\ 8 <= e_len e <= 5440 /\
garr8 segs (mrestrict (w_H W) mem) (e_pp e) (hd_zbytes (Layout.pp_bytes r)) /\
0 <= e_cap e <= 9 /\ 0 <= e_null e <= 1 /\
e_rc e = ans_rc (Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e)).

(* ---------------- C2 0x82e60: what headamp_build_contract's post gives the malloc(pod) step ---------------- *)
Definition hq_cut_C2 (hx : hq_hcx segs) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hq_at_cut segs B LLVMF_STK hx pos e 1 [(e_pp e, Layout.PP_SIZE)] (hi_L2 headamp_himg_A) (hi_shA headamp_himg_A)
  ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hq_recP e r W mem.

(* ---------------- C3 0x82e64: what M02 (headamp_dup_contract) starts from ---------------- *)
Definition hq_cut_C3 (hx : hq_hcx segs) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
ly S W regs mem md : Prop :=
hq_at_cut segs B LLVMF_STK hx pos e 2 [(e_pp e, Layout.PP_SIZE); (e_pod e, e_len e)] (hi_L3 headamp_himg_A)
  (hi_shA headamp_himg_A) ly S W regs mem md /\
YK0o.frm_zero (@fp_csr fx2) /\
hq_recP e r W mem /\
range_addressable (aview segs (w_H W) mem) SHADOW_OFF (e_pod e) (e_len e) /\
shadow_hull_vis (aview segs (w_H W) mem) (e_pod e) (e_len e) /\
amem_range (e_pod e) (e_len e + 8) /\ e_pod e mod 16 = 0.

(* ---------------- the allocator step C2 -> C3: the `jal` of malloc(pod) ---------------- *)
Definition hq_at_C3 (hx : hq_hcx segs) (fx2 : YK11.FPState) (pos : Z) (e : hd_env) (r : Model.pod_rec)
(ly2 : alayout) (S2 : astate) (W2 : world segs) (regs2 : bvmap 5 word) (mem2 : word -> option byte)
: world segs -> config -> Prop :=
fun W3 c3 => exists pod ly3 S3 regs3 mem3 md3,
c3 = @cfg_at fx2 segs HQ_C3 regs3 mem3 md3 /\
4096 <= pod /\ getr regs3 10 = w64 pod /\
(forall rr, acallee_saved rr -> getr regs3 (Z_to_bv 5 rr) = getr regs2 (Z_to_bv 5 rr)) /\
frames S3 = frames S2 /\
ablocks B ly3 S3 = ablocks B ly2 S2 ++ [(pod, e_len e)] /\
acall_kept segs B ly2 S2 W2 mem2 W3 mem3 (e_R e - ASTACK) (e_R e)
  (fun a => pod <= a < pod + req_size (e_len e)) /\
hq_cut_C3 hx fx2 pos (hq_env_pod e pod) r ly3 S3 W3 regs3 mem3 md3.

(* the malloc(pod) step: a0 = len + (len == 0) = len (8 <= len) from 0x82e58 .. 0x82e5c *)
Definition hq_S_C23_stmt : Prop :=
forall (hx : hq_hcx segs) (fx2 : YK11.FPState) pos e r ly2 S2 W2 regs2 mem2 md2,
hq_base segs B RLO RHI RA_LLVMF A_EMPTY EV_LIB LIVE_LIB LLVMF_STK hx ->
hq_cut_C2 hx fx2 pos e r ly2 S2 W2 regs2 mem2 md2 ->
SRr segs W2 (@cfg_at fx2 segs HQ_C2 regs2 mem2 md2) (hq_at_C3 hx fx2 pos e r ly2 S2 W2 regs2 mem2).

End c.
End b.

Print Assumptions hq_c23_himg.
Print Assumptions hq_env_pod_xv.
