(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; every address below is measured on the
   unstripped twin b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the piece "x->rc and the last four checks" of the walk of LLVMFuzzerTestOneInput
   (0x80bc0), lib/A/HPgSegM.v hq_piece_M3e_rc_stmt: from RC 0x83694 and RCM 0x8369c to FIRST 0x83724. Proves no
   function (kind: segment lemma).

   THE WALK (the blocks: lib/A/HPgM3eRcBlk.v)
   - RC: he_blk_rc loads x (R+0x108) into s2 and x->n into a1; x->n is the number of cells expect_of wrote, which
     is its rc (hq_cut_RC), so the state at 0x8369c is RCM's cut.
   - RCM: he_blk_rcm stores a1 = expect_of's rc into x->rc: x then holds Spec/HeadBytes.v x_bytes of expect_of's
     answer (hq_x_open with the rc word written; he_x_store). From here every state up to 0x836dc is he_mid: what
     M03 carries (HPgSegM.hq_base3, x in scope), the values the code reads (rc, res, out, x), and x's 136 bytes.
   - The four calls check_object 0x8405c, check_cells 0x84148, check_keys 0x842e8, check_refusal 0x84368 go through
     lib/A/HPgCalls.v's adapters with their contracts (Section hypotheses CKO, CKC, CKK, CKR, at every float state);
     every premise of a contract comes from lib/A/HPgSiteA.v's call-site lemmas (headamp_A_site_object / _cells /
     _keys / _refusal), whose inputs he_mid carries (he_site): res and out hold the parse's answer, x holds
     expect_of's.
   - 0x836c0 `bltz s11` skips check_keys and check_refusal when rc < 0 (he_blk_cells_ret).
   - 0x836dc li a0,-8 (he_blk_li), then x's 17 shadow granules := 0xf8 (HPgSteps.hd_scope_x_out), so the frame's
     shadow is image A's hi_shB again, and FIRST's cut holds: its continuation is the statement's.
   SECTION HYPOTHESES: MTL : ameter_laws MT, errno_low : api_env rsegs B (as HPgM3eBase), and the four check
   contracts at their entries, at every float state: CKO : forall fy, hd_check_object_specX (fx := fy) rsegs B MT
   A_CK_OBJECT; CKC (check_cells, A_CK_CELLS); CKK (check_keys, A_CK_KEYS); CKR (check_refusal, A_CK_REFUSAL). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0m.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Cursor Model Layout Accessors.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgSeg HPgSegM.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgMem HPgCalls HPgSteps HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgM3eBase HPgM3eRcBlk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= registers ======================================= *)
Lemma he_r5 : forall (b : bv 5) q, bv_unsigned b = q -> Z_to_bv 5 q = b.
Proof.
intros b q <-. apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap. apply Z.mod_small. apply bv_unsigned_in_range.
Qed.

Lemma he_notin : forall q (clob : list (bv 5)), forallb (fun b => negb (bv_unsigned b =? q)) clob = true ->
0 <= q < 32 -> ~ In (Z_to_bv 5 q) clob.
Proof.
intros q clob H Hq Hin. rewrite forallb_forall in H. specialize (H _ Hin).
rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 5) with 32 in H.
rewrite Z.mod_small in H by lia. rewrite Z.eqb_refl in H. discriminate H.
Qed.

(* a register outside a block's clobber list *)
Lemma he_kr : forall (regs regs' : bvmap 5 word) (clob : list (bv 5)) q,
(forall r : bv 5, bv_unsigned r <> 0 -> ~ In r clob -> getr regs' r = getr regs r) ->
0 < q < 32 -> forallb (fun b => negb (bv_unsigned b =? q)) clob = true ->
getr regs' (Z_to_bv 5 q) = getr regs (Z_to_bv 5 q).
Proof.
intros regs regs' clob q H Hq Hc. apply H; [|apply he_notin; [exact Hc | lia]].
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
Qed.

(* a block's clobber list avoids sp, gp and tp *)
Ltac he_clob := let q := fresh "q" in let Hq := fresh "Hq" in
  intros q Hq; apply he_notin; [destruct Hq as [ -> | [ -> | -> ] ]; vm_compute; reflexivity | lia].

(* ======================================= x's bytes ======================================= *)
(* the null flag's two readings *)
Lemma he_null_flag : forall null, 0 <= null <= 1 -> negb (null =? 0) = (null =? 1).
Proof. intros null Hn. destruct (Z.eq_dec null 0) as [ -> | H ]; [reflexivity|]. replace null with 1 by lia. reflexivity. Qed.

(* x after the rc store: x_bytes of expect_of's answer is hq_x_open with the rc word written *)
Lemma he_x_bytes : forall (o : answer),
ans_n o = Z.of_nat (length (ans_cells o)) ->
x_bytes o = Mem.le4 (Z_to_bv 64 (ans_rc o)) ++ skipn 4 (hq_x_open (ans_cells o) (ans_keys o) (ans_rf o)).
Proof. intros o Hn. unfold x_bytes, ans_res_bytes, hq_x_open. rewrite Hn. reflexivity. Qed.

Lemma he_x_open_split : forall cs keys rf,
hq_x_open cs keys rf = repeat (Z_to_bv 8 0) 4 ++ skipn 4 (hq_x_open cs keys rf).
Proof. intros cs keys rf. unfold hq_x_open. reflexivity. Qed.

(* the word x->n at x + 0x7c *)
Lemma he_x_n : forall H mem a cs keys rf, (length cs <= X_CELLS)%nat ->
garr8 rsegs (mrestrict H mem) a (hd_zbytes (hq_x_open cs keys rf)) ->
garr8 rsegs (mrestrict H mem) (a + 0x7c) (hd_zbytes (Mem.le4 (Z_to_bv 64 (Z.of_nat (length cs))))).
Proof.
intros H mem a cs keys rf Hl Hg. apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
apply (proj2 (hm_bytes_zbytes rsegs _ _ _ _)) in Hg. unfold hq_x_open, ha_res_bytes in Hg.
rewrite (app_assoc (repeat (Z_to_bv 8 0) 4)), (app_assoc (repeat (Z_to_bv 8 0) 4 ++ x_cells_bytes cs)) in Hg.
apply hm_bytes_app in Hg as [_ Hg]. apply hm_bytes_app in Hg as [Hg _].
rewrite !length_app, repeat_length, length_x_cells_bytes, repeat_length in Hg.
unfold X_CELLS in *.
replace (a + 0x7c) with (a + Z.of_nat (4 + 12 * length cs + 12 * (10 - length cs))) by lia.
exact Hg.
Qed.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis errno_low : api_env rsegs B.
Hypothesis CKO : forall fy : YK11.FPState, hd_check_object_specX (fx := fy) rsegs B MT A_CK_OBJECT.
Hypothesis CKC : forall fy : YK11.FPState, hd_check_cells_specX (fx := fy) rsegs B MT A_CK_CELLS.
Hypothesis CKK : forall fy : YK11.FPState, hd_check_keys_specX (fx := fy) rsegs B MT A_CK_KEYS.
Hypothesis CKR : forall fy : YK11.FPState, hd_check_refusal_specX (fx := fy) rsegs B MT A_CK_REFUSAL.

Section p.
Variable cx : hs_scx rsegs.
Variable r : Model.pod_rec.
Variable POST : world rsegs -> config -> Prop.
Variable ev : Z.
Hypothesis HS : @hq_start_M03 fx rc SK rsegs B cx r ev.
Hypothesis HFIRST : @hq_from_FIRST fx rc SK rsegs B MT cx r POST.

(* the registers the walk keeps from RCM to FIRST (all callee-saved) *)
Definition he_keep : list Z := [8; 9; 18; 19; 22; 23; 24; 25; 26; 27].
(* the values the walk reads from RCM on, besides hq_L_seg's *)
Definition he_L : list (hd_loc * Z) :=
  [(LReg 18, e_F (x_e rsegs cx) + HQ_XO);
   (LCell XR 0x20, e_F (x_e rsegs cx)); (LCell XR 0x60, e_F (x_e rsegs cx)); (LCell XR 0xf0, e_pp (x_e rsegs cx));
   (LCell XR 0x110, hd_xv (x_e rsegs cx) XProps); (LCell XR 0x118, 3 * e_cap (x_e rsegs cx) + 3)].

(* a state between RCM's store and 0x836dc *)
Definition he_mid (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 : Prop :=
@hq_base3 fx rc SK rsegs B MT cx fx2 r hq_shX ly2 S2 W2 regs2 mem2 md2 /\
hs_at_cx rsegs cx W2 mem2 regs2 (hq_L_seg rsegs cx ++ he_L) /\
Model.corrupt r = false /\
garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + HQ_XO) (hd_zbytes (x_bytes (hq_exp rsegs cx r))).

Ltac he_in := cbn [hq_L_seg hq_L_frame he_L app In]; repeat (first [left; reflexivity | right]).

Lemma he_at_reg : forall W mem regs L q v (b : bv 5), hs_at_cx rsegs cx W mem regs L -> In (LReg q, v) L ->
bv_unsigned b = q -> getr regs b = w64 v.
Proof.
intros W mem regs L q v b H Hin Hb. rewrite <- (he_r5 b q Hb). exact (proj1 (Forall_forall _ _) H _ Hin).
Qed.
Lemma he_at_cell : forall W mem regs L o v, hs_at_cx rsegs cx W mem regs L -> In (LCell XR o, v) L ->
val_mem rsegs (mrestrict (w_H W) mem) (e_R (x_e rsegs cx) + o) 8 (v mod 2 ^ 64).
Proof. intros W mem regs L o v H Hin. exact (proj1 (Forall_forall _ _) H _ Hin). Qed.
Lemma he_at_sub : forall W mem regs L1 L2, hs_at_cx rsegs cx W mem regs L1 -> (forall f, In f L2 -> In f L1) ->
hs_at_cx rsegs cx W mem regs L2.
Proof.
intros W mem regs L1 L2 H Hs. unfold hs_at_cx, hs_at in *. rewrite Forall_forall in *. intros f Hf. exact (H f (Hs f Hf)).
Qed.

(* the segment's geometry, once *)
Lemma he_geo :
4096 <= e_F (x_e rsegs cx) /\ e_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\ e_F (x_e rsegs cx) mod 32 = 0 /\
in_app (e_F (x_e rsegs cx)) 1024 /\
alloc_ceiling + T_SEG_STK <= e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) <= 2 ^ 47 /\
0x7fff8000 <= shadow_addr (e_F (x_e rsegs cx)) /\ shadow_addr (e_F (x_e rsegs cx)) + 128 <= 0x10007fef8080 /\
0x10007fff8000 <= alloc_ceiling /\
0 <= e_cap (x_e rsegs cx) <= 9 /\ 0 <= e_null (x_e rsegs cx) <= 1.
Proof.
pose proof HS as (HP & _).
destruct (he_seg B cx _ HP) as (_ & _ & _ & HF32 & HF4 & HFc & HFapp & _ & HR & HR47 & _ & Hcap & Hnull).
pose proof (he_fsh_rng B cx _ HP) as [Hs1 Hs2].
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
split; [exact HF4|]. split; [exact HFc|]. split; [exact HF32|]. split; [exact HFapp|].
split; [exact HR|]. split; [exact HR47|]. split; [exact Hs1|]. split; [exact Hs2|].
split; [lia|]. split; [exact Hcap | exact Hnull].
Qed.

(* F, the frame's address at the segment's start, at any state of the journal *)
Lemma he_F_at : forall ly2 S2 W2 mem2 md2,
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem2 md2 (x_k rsegs cx) ->
e_F (x_e rsegs cx) = frame_addr ly2 4 (x_pos rsegs cx).
Proof.
intros ly2 S2 W2 mem2 md2 HJ.
pose proof HS as (HP & _).
destruct (he_seg B cx _ HP) as (_ & _ & HF & _).
pose proof HP as (HJ0 & _).
assert (E1 : frame_addr (x_lyc rsegs cx) 4 (x_pos rsegs cx) = frame_addr (x_ly rsegs cx) 4 (x_pos rsegs cx))
  by (eapply hc_frame_addr_j; exact HJ0).
assert (E2 : frame_addr ly2 4 (x_pos rsegs cx) = frame_addr (x_ly rsegs cx) 4 (x_pos rsegs cx))
  by (eapply hc_frame_addr_j; exact HJ).
rewrite HF, E1, E2. reflexivity.
Qed.

(* ======================================= he_mid across a step ======================================= *)
Lemma he_mid_kept : forall fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (Wr : Z -> Prop),
he_mid fx2 ly2 S2 W2 regs2 mem2 md2 ->
hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3 ->
(forall a, Wr a -> e_R (x_e rsegs cx) - T_SEG_STK <= a < e_R (x_e rsegs cx)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ Wr a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
(forall q, In q he_keep -> getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)) ->
he_mid fx2 ly3 S3 W3 regs3 mem3 md3.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Wr Hm Hcore3 HWr Hk Hr.
destruct he_geo as (HF4 & HFc & HF32 & HFapp & HR & HR47 & Hs1 & Hs2 & Hc1 & Hcap & Hnull).
unfold T_SEG_STK, ASTACK in *.
destruct Hm as (Hb & Hat & Hcor & Hx).
pose proof Hb as (_ & Hfx & Hfsh & _).
assert (Hk' : forall a, 0 <= a < 2 ^ 64 -> ~ he_wz cx a ->
  aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. apply Hk; [exact Ha|]. intros HW. apply Hn. left. pose proof (HWr a HW) as H.
  unfold T_SEG_STK, ASTACK. exact H. }
split.
{ refine (he_base3_kept B MT errno_low cx r ev fx2 fx2 hq_shX hq_shX _ _ _ _ _ _ _ _ _ _ _ _ HS Hb Hcore3 Hk' _ Hfx).
  unfold hs_fsh_at in *. apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh).
  intros i Hi. rewrite hq_shX_len in Hi. apply Hk; [lia|]. intros HW. apply HWr in HW. lia. }
split.
{ unfold hs_at_cx, hs_at in *. apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ Hat).
  intros f Hf. cbn [hq_L_seg hq_L_frame he_L app] in Hf.
  repeat (destruct Hf as [<-|Hf];
   [cbn [fst hm_keeps hd_xv];
    first [ apply Hr; unfold he_keep; cbn [In]; lia
          | let i := fresh "i" in let Hi := fresh "Hi" in
            intros i Hi; apply Hk; [lia | intros HW; apply HWr in HW; lia] ] | ]).
  destruct Hf. }
split; [exact Hcor|].
pose proof HS as (HP & _).
destruct (he_ans_ok cx r Hcap) as (_ & Hlc & _).
rewrite <- (he_ans_exp cx r (proj1 (proj2 (proj2 HS))) Hcor Hnull) in Hx |- *.
apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (hm_bytes_zbytes rsegs _ _ _ _) Hx)|].
intros a Ha. rewrite (length_x_bytes _ Hlc) in Ha. unfold HQ_XO in Ha.
apply Hk; [lia|]. intros HW. apply HWr in HW. lia.
Qed.

(* ======================================= the call sites ======================================= *)
Lemma he_site : forall fx2 ly2 S2 W2 regs2 mem2 md2 ret,
he_mid fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 1 = w64 ret -> 4096 <= ret < 2 ^ 64 -> ret mod 2 = 0 ->
hd_pre rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
  (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx) T_check_STK regs2 ly2 S2 W2 mem2 md2 /\
In (hi_cid headamp_himg_A, x_pos rsegs cx) (x_own rsegs cx) /\
e_F (x_e rsegs cx) = frame_addr ly2 (hi_cid headamp_himg_A) (x_pos rsegs cx) /\
hd_fsh rsegs (w_H W2) mem2 (e_F (x_e rsegs cx)) headamp_A_shX /\
Model.pod_rec_wf r /\ Model.corrupt r = false /\ 0 <= e_cap (x_e rsegs cx) <= 9 /\
garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x180) (hd_zbytes (ans_res_bytes (hq_ans rsegs cx r))) /\
garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x1a0)
  (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null (x_e rsegs cx) =? 0)) (e_cap (x_e rsegs cx)) r))).
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 ret Hm H1 Hret1 Hret2.
pose proof HS as (HP & _ & Hwf & _).
destruct (he_seg B cx _ HP) as (_ & Hown & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & Hnull).
destruct Hm as (Hb & Hat & Hcor & Hx). pose proof Hb as (Hcore & _ & Hfsh & _ & _ & _ & _ & Hres & _).
pose proof Hcore as (HJ & _).
split.
{ apply (hc_pre rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (e_R (x_e rsegs cx)) ret T_check_STK
    (he_hc_core B MT cx _ _ _ _ _ _ _ _ HP Hcore) H1 Hret1 Hret2).
  unfold T_check_STK, T_SEG_STK, ASTACK. lia. }
split; [exact Hown|].
split; [exact (he_F_at _ _ _ _ _ HJ)|].
split; [unfold hs_fsh_at in Hfsh; exact Hfsh|].
split; [exact Hwf|]. split; [exact Hcor|]. split; [exact Hcap|].
split; [exact Hres|].
rewrite (he_null_flag _ Hnull). exact Hx.
Qed.

(* the answer's rc lies in [-1, 9] *)
Lemma he_rc_rng : - 2 ^ 31 <= e_rc (x_e rsegs cx) < 2 ^ 31.
Proof.
destruct he_geo as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hcap & _).
destruct (he_ans_ok cx r Hcap) as (HO & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrc & _).
rewrite Hrc. apply answer_ok_parts in HO as [[(E & _) | (E & _)] _]; lia.
Qed.

(* ======================================= 0x836dc .. FIRST ======================================= *)
Lemma he_from_ref_ret : forall fx2 ly2 S2 W2 regs2 mem2 md2,
he_mid fx2 ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs HE_REF_RET regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 Hm.
pose proof HS as (HP & _).
destruct (he_seg B cx _ HP) as (_ & Hown & _).
destruct he_geo as (HF4 & HFc & HF32 & HFapp & HR & HR47 & Hs1 & Hs2 & Hc1 & Hcap & Hnull).
unfold T_SEG_STK, ASTACK in HR.
pose proof Hm as (Hb & Hat & Hcor & Hx).
pose proof Hb as (Hcore & Hfx & Hfsh & _).
pose proof Hcore as (HJ & _).
eapply SRr_bind; [exact (he_blk_li (fx := fx2) B MT MTL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 HJ)|].
intros W3 c3 Hle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & Hmem3 & H10).
assert (Hcore3 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (he_core_blk B MT MTL cx _ (fun _ => False) [10%bv] _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 Hkr3 _
    Hfr3 Hperm3 Hio3 Hmo3 Hmem3 (fun a (H : False) => match H with end)). he_clob. }
pose proof (he_F_at _ _ _ _ _ HJ3) as HF3.
assert (H19 : getr regs3 19 = w64 (shadow_addr (frame_addr ly3 4 (x_pos rsegs cx)))).
{ rewrite <- HF3. rewrite <- (he_r5 19%bv 19 eq_refl).
  rewrite (he_kr regs2 regs3 [10%bv] 19 Hkr3 ltac:(lia) ltac:(vm_compute; reflexivity)).
  rewrite (he_r5 19%bv 19 eq_refl). apply (he_at_reg _ _ _ _ 19 _ _ Hat); [he_in | reflexivity]. }
change (mkCfg (mkst regs3 (w64 HE_XOUT) mem3 (seg_rom rsegs)) md3) with (@cfg_at fx2 rsegs 0x836e0 regs3 mem3 md3).
eapply SRr_bind.
{ refine (hd_scope_x_out (fx := fx2) B MT MTL (AR_laws_ok rsegs B) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3 4
    (x_pos rsegs cx) HJ3 Hown ltac:(lia) H19 H10 _ _ _);
  [rewrite <- HF3; lia | rewrite <- HF3; lia | vm_compute; discriminate]. }
intros W4 c4 Hle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & Hkr4 & Hfr4 & Hperm4 & Hio4 & Hmo4 & Hmem4 & Hsh4).
rewrite <- HF3 in Hmem4, Hsh4.
assert (Hcore4 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly4 S4 W4 regs4 mem4 md4).
{ refine (he_core_blk B MT MTL cx _ _ [] _ _ _ _ _ _ _ _ _ _ _ _ Hcore3 HJ4 Hkr4 _ Hfr4 Hperm4 Hio4 Hmo4 Hmem4 _);
  [he_clob|]. intros a Ha. left. unfold hd_inw. cbn [hi_w3 headamp_himg_A].
  apply Exists_cons_tl, Exists_cons_hd. cbn [hd_xv fst snd]. lia. }
assert (Hk42 : forall a, 0 <= a < 2 ^ 64 -> ~ (shadow_addr (e_F (x_e rsegs cx)) + 52 <= a <
  shadow_addr (e_F (x_e rsegs cx)) + 69) -> aview rsegs (w_H W4) mem4 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hn. rewrite (Hmem4 a Ha Hn). exact (Hmem3 a Ha (fun H => H)). }
apply (HFIRST fx2 ly4 S4 W4 regs4 mem4 md4).
split.
{ refine (he_base3_kept B MT errno_low cx r ev fx2 fx2 hq_shX (hi_shB headamp_himg_A) _ _ _ _ _ _ _ _ _ _ _ _
    HS Hb Hcore4 _ _ Hfx).
  - intros a Ha Hn. apply Hk42; [exact Ha|]. intros Hw. apply Hn. right. right. exact Hw.
  - replace (hi_shB headamp_himg_A) with (hm_setn hq_shX 52 17 248) by (vm_compute; reflexivity).
    unfold hs_fsh_at in *. apply (hm_fsh_set rsegs (w_H W2) mem2 (w_H W4) mem4 _ hq_shX 52 17 248 Hfsh).
    + intros i Hi. rewrite (Hsh4 i ltac:(lia)). reflexivity.
    + intros i Hi Hn. rewrite hq_shX_len in Hi. apply Hk42; [lia | lia]. }
assert (Hat2 : hs_at_cx rsegs cx W2 mem2 regs2
  (hq_L_frame rsegs cx ++
   [(LReg 22, e_cap (x_e rsegs cx)); (LReg 24, e_out (x_e rsegs cx)); (LReg 25, e_pod (x_e rsegs cx));
    (LReg 27, e_rc (x_e rsegs cx));
    (LCell XR 0x20, e_F (x_e rsegs cx)); (LCell XR 0x60, e_F (x_e rsegs cx)); (LCell XR 0xf0, e_pp (x_e rsegs cx));
    (LCell XR 0x110, hd_xv (x_e rsegs cx) XProps); (LCell XR 0x118, 3 * e_cap (x_e rsegs cx) + 3)])).
{ apply (he_at_sub _ _ _ _ _ Hat). intros f Hf. cbn [hq_L_frame app] in Hf.
  repeat (destruct Hf as [<-|Hf]; [he_in|]). destruct Hf. }
unfold hs_at_cx, hs_at in *. apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ Hat2).
intros f Hf. cbn [hq_L_frame app] in Hf.
repeat (destruct Hf as [<-|Hf];
 [cbn [fst hm_keeps hd_xv];
  first [ etransitivity; [apply (he_kr regs3 regs4 []); [exact Hkr4 | lia | vm_compute; reflexivity]|];
          apply (he_kr regs2 regs3 [10%bv]); [exact Hkr3 | lia | vm_compute; reflexivity]
        | let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; apply Hk42; lia ] | ]).
destruct Hf.
Qed.

(* ======================================= 0x836d0: check_refusal ======================================= *)
Lemma he_from_keys_ret : forall fx2 ly2 S2 W2 regs2 mem2 md2,
he_mid fx2 ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs HE_KEYS_RET regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 Hm.
pose proof HS as (HP & _).
destruct he_geo as (HF4 & HFc & HF32 & HFapp & HR & HR47 & Hs1 & Hs2 & Hc1 & Hcap & Hnull).
pose proof Hm as (Hb & Hat & Hcor & Hx). pose proof Hb as (Hcore & _). pose proof Hcore as (HJ & _).
eapply SRr_bind; [exact (he_blk_keys_ret (fx := fx2) B MT MTL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 HJ)|].
intros W3 c3 Hle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & Hmem3 & (H1 & H10 & H11)).
assert (Hcore3 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (he_core_blk B MT MTL cx _ (fun _ => False) [1%bv; 10%bv; 11%bv] _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 Hkr3 _
    Hfr3 Hperm3 Hio3 Hmo3 Hmem3 (fun a (H : False) => match H with end)). he_clob. }
assert (Hm3 : he_mid fx2 ly3 S3 W3 regs3 mem3 md3).
{ apply (he_mid_kept fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (fun _ => False) Hm Hcore3);
  [intros a [] | exact Hmem3 |].
  intros q Hq. unfold he_keep in Hq. apply (he_kr regs2 regs3 _ q Hkr3);
  [cbn [In] in Hq; lia | cbn [In] in Hq; repeat (destruct Hq as [<-|Hq]; [vm_compute; reflexivity|]); destruct Hq]. }
change (mkCfg (mkst regs3 (w64 HE_CK_REFUSAL) mem3 (seg_rom rsegs)) md3)
  with (@cfg_at fx2 rsegs A_CK_REFUSAL regs3 mem3 md3).
destruct (he_site fx2 ly3 S3 W3 regs3 mem3 md3 RA_CK_REFUSAL Hm3 H1 ltac:(unfold RA_CK_REFUSAL; lia) eq_refl)
  as (HPre & Hown & HFa & Hsh & Hwf & Hcor3 & Hcap3 & Hres & Hxb).
destruct (headamp_A_site_refusal rsegs B _ _ _ _ _ _ _ _ _ _ regs3 ly3 S3 W3 mem3 md3 (x_e rsegs cx) (x_pos rsegs cx) r
  (hq_ans rsegs cx r) HPre Hown HFa Hsh Hwf Hcor3 Hcap3 eq_refl Hres Hxb)
  as (Hr4 & Hx4 & Vr & Vx & RAr & RAx & Or & Ox & Ar & Ax & Hd).
refine (hc_check_refusal_call (fx := fx2) rsegs B MT (CKR fx2) POST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3
  (e_R (x_e rsegs cx)) _ _ _ (he_hc_core B MT cx _ _ _ _ _ _ _ _ HP Hcore3) H1 _ _ Hr4 Hx4 Vr Vx RAr RAx Or Ox Ar Ax Hd _).
{ rewrite H10. apply (he_at_reg _ _ _ _ 26 _ _ (proj1 (proj2 Hm))); [he_in | reflexivity]. }
{ rewrite H11. apply (he_at_reg _ _ _ _ 18 _ _ (proj1 (proj2 Hm))); [he_in | reflexivity]. }
intros W4 ly4 S4 regs4 mem4 md4 Hle4 Hcc4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hmem4.
assert (Hcore4 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly4 S4 W4 regs4 mem4 md4)
  by exact (he_core_call B MT MTL cx _ _ T_check_STK _ _ _ _ _ _ _ _ _ _ _ _ HP Hcore3
    ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) Hcc4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hmem4).
apply (he_from_ref_ret fx2 ly4 S4 W4 regs4 mem4 md4).
apply (he_mid_kept fx2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4
  (fun a => e_R (x_e rsegs cx) - T_check_STK <= a < e_R (x_e rsegs cx)) Hm3 Hcore4); [| exact Hmem4 |].
- intros a Ha. unfold T_check_STK, T_SEG_STK, ASTACK in *. lia.
- intros q Hq. apply Hpres4. unfold acallee_saved. unfold he_keep in Hq. cbn [In] in Hq. lia.
Qed.

(* ======================================= 0x836c0: bltz, check_keys ======================================= *)
Lemma he_from_cells_ret : forall fx2 ly2 S2 W2 regs2 mem2 md2,
he_mid fx2 ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs HE_CELLS_RET regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 Hm.
pose proof HS as (HP & _).
destruct he_geo as (HF4 & HFc & HF32 & HFapp & HR & HR47 & Hs1 & Hs2 & Hc1 & Hcap & Hnull).
pose proof Hm as (Hb & Hat & Hcor & Hx). pose proof Hb as (Hcore & _). pose proof Hcore as (HJ & _).
assert (H27 : getr regs2 27 = w64 (e_rc (x_e rsegs cx))) by (apply (he_at_reg _ _ _ _ 27 _ _ Hat); [he_in | reflexivity]).
eapply SRr_bind;
  [exact (he_blk_cells_ret (fx := fx2) B MT MTL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 _ HJ H27 he_rc_rng)|].
intros W3 c3 Hle3 [(Hlt & (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & Hmem3 & _))
                  |(Hge & (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & Hmem3 &
                           (H1 & H10 & H11)))].
- assert (Hcore3 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
  { refine (he_core_blk B MT MTL cx _ (fun _ => False) [] _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 Hkr3 _
      Hfr3 Hperm3 Hio3 Hmo3 Hmem3 (fun a (H : False) => match H with end)). he_clob. }
  apply (he_from_ref_ret fx2 ly3 S3 W3 regs3 mem3 md3).
  apply (he_mid_kept fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (fun _ => False) Hm Hcore3);
  [intros a [] | exact Hmem3 |].
  intros q Hq. unfold he_keep in Hq. apply (he_kr regs2 regs3 _ q Hkr3);
  [cbn [In] in Hq; lia | cbn [In] in Hq; repeat (destruct Hq as [<-|Hq]; [vm_compute; reflexivity|]); destruct Hq].
- assert (Hcore3 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
  { refine (he_core_blk B MT MTL cx _ (fun _ => False) [1%bv; 10%bv; 11%bv] _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3 Hkr3 _
      Hfr3 Hperm3 Hio3 Hmo3 Hmem3 (fun a (H : False) => match H with end)). he_clob. }
  assert (Hm3 : he_mid fx2 ly3 S3 W3 regs3 mem3 md3).
  { apply (he_mid_kept fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (fun _ => False) Hm Hcore3);
    [intros a [] | exact Hmem3 |].
    intros q Hq. unfold he_keep in Hq. apply (he_kr regs2 regs3 _ q Hkr3);
    [cbn [In] in Hq; lia | cbn [In] in Hq; repeat (destruct Hq as [<-|Hq]; [vm_compute; reflexivity|]); destruct Hq]. }
  change (mkCfg (mkst regs3 (w64 HE_CK_KEYS) mem3 (seg_rom rsegs)) md3)
    with (@cfg_at fx2 rsegs A_CK_KEYS regs3 mem3 md3).
  destruct (he_site fx2 ly3 S3 W3 regs3 mem3 md3 RA_CK_KEYS Hm3 H1 ltac:(unfold RA_CK_KEYS; lia) eq_refl)
    as (HPre & Hown & HFa & Hsh & Hwf & Hcor3 & Hcap3 & Hres & Hxb).
  destruct (headamp_A_site_keys rsegs B _ _ _ _ _ _ _ _ _ _ regs3 ly3 S3 W3 mem3 md3 (x_e rsegs cx) (x_pos rsegs cx) r
    (hq_ans rsegs cx r) HPre Hown HFa Hsh Hwf Hcor3 Hcap3 eq_refl Hres Hxb)
    as (Hr4 & Hx4 & Vr & Vx & RAr & RAx & Or & Ox & Ar & Ax & Hd).
  refine (hc_check_keys_call (fx := fx2) rsegs B MT (CKK fx2) POST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3
    (e_R (x_e rsegs cx)) _ _ _ (he_hc_core B MT cx _ _ _ _ _ _ _ _ HP Hcore3) H1 _ _ Hr4 Hx4 Vr Vx RAr RAx Or Ox Ar Ax Hd _).
  { rewrite H10. apply (he_at_reg _ _ _ _ 26 _ _ Hat); [he_in | reflexivity]. }
  { rewrite H11. apply (he_at_reg _ _ _ _ 18 _ _ Hat); [he_in | reflexivity]. }
  intros W4 ly4 S4 regs4 mem4 md4 Hle4 Hcc4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hmem4.
  assert (Hcore4 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly4 S4 W4 regs4 mem4 md4)
    by exact (he_core_call B MT MTL cx _ _ T_check_STK _ _ _ _ _ _ _ _ _ _ _ _ HP Hcore3
      ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) Hcc4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hmem4).
  apply (he_from_keys_ret fx2 ly4 S4 W4 regs4 mem4 md4).
  apply (he_mid_kept fx2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4
    (fun a => e_R (x_e rsegs cx) - T_check_STK <= a < e_R (x_e rsegs cx)) Hm3 Hcore4); [| exact Hmem4 |].
  + intros a Ha. unfold T_check_STK, T_SEG_STK, ASTACK in *. lia.
  + intros q Hq. apply Hpres4. unfold acallee_saved. unfold he_keep in Hq. cbn [In] in Hq. lia.
Qed.

(* ======================================= 0x836b0: check_cells ======================================= *)
Lemma he_from_obj_ret : forall fx2 ly2 S2 W2 regs2 mem2 md2,
he_mid fx2 ly2 S2 W2 regs2 mem2 md2 ->
SRr rsegs W2 (@cfg_at fx2 rsegs HE_OBJ_RET regs2 mem2 md2) POST.
Proof.
intros fx2 ly2 S2 W2 regs2 mem2 md2 Hm.
pose proof HS as (HP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Houtb & _ & _ & Hrc & _).
destruct Houtb as (_ & Houtin & _).
destruct he_geo as (HF4 & HFc & HF32 & HFapp & HR & HR47 & Hs1 & Hs2 & Hc1 & Hcap & Hnull).
pose proof Hm as (Hb & Hat & Hcor & Hx). pose proof Hb as (Hcore & _ & _ & _ & _ & _ & Hout & _).
pose proof Hcore as (HJ & _).
eapply SRr_bind; [exact (he_blk_obj_ret (fx := fx2) B MT MTL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 HJ)|].
intros W3 c3 Hle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & Hmem3 &
  (H1 & H10 & H11 & H12)).
assert (Hcore3 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (he_core_blk B MT MTL cx _ (fun _ => False) [1%bv; 10%bv; 11%bv; 12%bv] _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3
    Hkr3 _ Hfr3 Hperm3 Hio3 Hmo3 Hmem3 (fun a (H : False) => match H with end)). he_clob. }
assert (Hm3 : he_mid fx2 ly3 S3 W3 regs3 mem3 md3).
{ apply (he_mid_kept fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (fun _ => False) Hm Hcore3);
  [intros a [] | exact Hmem3 |].
  intros q Hq. unfold he_keep in Hq. apply (he_kr regs2 regs3 _ q Hkr3);
  [cbn [In] in Hq; lia | cbn [In] in Hq; repeat (destruct Hq as [<-|Hq]; [vm_compute; reflexivity|]); destruct Hq]. }
change (mkCfg (mkst regs3 (w64 HE_CK_CELLS) mem3 (seg_rom rsegs)) md3)
  with (@cfg_at fx2 rsegs A_CK_CELLS regs3 mem3 md3).
destruct (he_site fx2 ly3 S3 W3 regs3 mem3 md3 RA_CK_CELLS Hm3 H1 ltac:(unfold RA_CK_CELLS; lia) eq_refl)
  as (HPre & Hown & HFa & Hsh & Hwf & Hcor3 & Hcap3 & Hres & Hxb).
pose proof Hm3 as (Hb3 & _). pose proof Hb3 as (Hcore3' & _ & _ & _ & _ & _ & Hout3 & _).
pose proof Hcore3' as (_ & _ & _ & Hperm3' & _).
assert (Hin3 : In (e_out (x_e rsegs cx), 3 * (e_cap (x_e rsegs cx) + 1)) (ablocks B ly3 S3))
  by exact (Permutation_in _ (Permutation_sym Hperm3') Houtin).
destruct (headamp_A_site_cells rsegs B _ _ _ _ _ _ _ _ _ _ regs3 ly3 S3 W3 mem3 md3 (x_e rsegs cx) (x_pos rsegs cx) r
  (hq_ans rsegs cx r) HPre Hown HFa Hsh Hin3 Hwf Hcor3 Hcap3 eq_refl Hout3 Hxb)
  as (Hrcb & Vx & RAx & Ox & Ax & Hal & Hpos).
refine (hc_check_cells_call (fx := fx2) rsegs B MT (CKC fx2) POST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3
  (e_R (x_e rsegs cx)) (ans_rc (hq_ans rsegs cx r)) (e_out (x_e rsegs cx)) (e_F (x_e rsegs cx) + 0x1a0)
  (ans_cells (hq_ans rsegs cx r)) (he_hc_core B MT cx _ _ _ _ _ _ _ _ HP Hcore3) H1 _ _ _
  Hrcb Vx RAx Ox Ax Hal Hpos _).
{ rewrite H10. apply (he_at_reg _ _ _ _ 24 _ _ Hat); [he_in | reflexivity]. }
{ rewrite H11, <- Hrc. apply (he_at_reg _ _ _ _ 27 _ _ Hat); [he_in | reflexivity]. }
{ rewrite H12. apply (he_at_reg _ _ _ _ 18 _ _ Hat); [he_in | reflexivity]. }
intros W4 ly4 S4 regs4 mem4 md4 Hle4 Hcc4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hmem4.
assert (Hcore4 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly4 S4 W4 regs4 mem4 md4)
  by exact (he_core_call B MT MTL cx _ _ T_check_STK _ _ _ _ _ _ _ _ _ _ _ _ HP Hcore3
    ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) Hcc4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hmem4).
apply (he_from_cells_ret fx2 ly4 S4 W4 regs4 mem4 md4).
apply (he_mid_kept fx2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4
  (fun a => e_R (x_e rsegs cx) - T_check_STK <= a < e_R (x_e rsegs cx)) Hm3 Hcore4); [| exact Hmem4 |].
- intros a Ha. unfold T_check_STK, T_SEG_STK, ASTACK in *. lia.
- intros q Hq. apply Hpres4. unfold acallee_saved. unfold he_keep in Hq. cbn [In] in Hq. lia.
Qed.

(* ======================================= RCM 0x8369c: x->rc, check_object ======================================= *)
(* x after the store of expect_of's rc at x *)
Lemma he_x_store : forall (W2 W3 : world rsegs) mem2 mem3,
hq_x_at rsegs cx W2 mem2 (ans_cells (hq_exp rsegs cx r)) (ans_keys (hq_exp rsegs cx r)) (ans_rf (hq_exp rsegs cx r)) ->
val_mem rsegs (mrestrict (w_H W3) mem3) (e_F (x_e rsegs cx) + HQ_XO) 4
  (bv_unsigned (w64 (ans_rc (hq_exp rsegs cx r))) mod 2 ^ 32) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (e_F (x_e rsegs cx) + HQ_XO <= a < e_F (x_e rsegs cx) + HQ_XO + 4) ->
 aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
garr8 rsegs (mrestrict (w_H W3) mem3) (e_F (x_e rsegs cx) + HQ_XO) (hd_zbytes (x_bytes (hq_exp rsegs cx r))).
Proof.
intros W2 W3 mem2 mem3 (Hg & Hl & _) V Hk.
destruct he_geo as (HF4 & HFc & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
rewrite (he_x_bytes _ (proj1 (he_exp_n cx r))).
apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)). apply hm_bytes_app. split.
- unfold Mem.le4. rewrite <- (Mem.Z_to_le_bytes_mod 4 _ 32) by lia. apply hm_bytes_of_val. exact V.
- rewrite Mem.length_le4. apply (hm_bytes_kept rsegs (w_H W2) mem2).
  + rewrite he_x_open_split in Hg. apply (proj2 (hm_bytes_zbytes rsegs _ _ _ _)) in Hg.
    apply hm_bytes_app in Hg as [_ Hg]. rewrite repeat_length in Hg. exact Hg.
  + intros a Ha. rewrite length_skipn, (hq_x_open_len _ _ _ Hl) in Ha. unfold HQ_XO in *.
    apply Hk; lia.
Qed.

Lemma he_from_RCM : @hq_from_RCM fx rc SK rsegs B MT cx r POST.
Proof.
unfold hq_from_RCM. intros fx2 ly2 S2 W2 regs2 mem2 md2 (Hb & Hat & Hcor & Hxat).
pose proof HS as (HP & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrc & _).
destruct (he_seg B cx _ HP) as (_ & Hown & _).
destruct he_geo as (HF4 & HFc & HF32 & HFapp & HR & HR47 & Hs1 & Hs2 & Hc1 & Hcap & Hnull).
pose proof (@ASAN_CEIL_range rc) as [[Hc1' Hc2'] _]. unfold ASAN_CEIL in Hc1', Hc2'.
pose proof Hb as (Hcore & Hfx & Hfsh & _). pose proof Hcore as (HJ & _).
pose proof (he_F_at _ _ _ _ _ HJ) as HF2.
assert (H18 : getr regs2 18 = w64 (e_F (x_e rsegs cx) + HQ_XO))
  by (apply (he_at_reg _ _ _ _ 18 _ _ Hat); [he_in | reflexivity]).
eapply SRr_bind.
{ refine (he_blk_rcm (fx := fx2) B MT MTL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (x_pos rsegs cx)
    (e_F (x_e rsegs cx) + HQ_XO) HJ Hown _ _ _ H18);
  [rewrite <- HF2; unfold HQ_XO; lia | rewrite <- HF2; unfold HQ_XO; lia | unfold HQ_XO; lia]. }
intros W3 c3 Hle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & Hmem3 &
  (H1 & H10 & H11 & H12 & Vst)).
assert (Hcore3 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (he_core_blk B MT MTL cx _ _ [1%bv; 10%bv; 11%bv; 12%bv] _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3
    Hkr3 _ Hfr3 Hperm3 Hio3 Hmo3 Hmem3 _); [he_clob|].
  intros a Ha. left. unfold hd_inw. cbn [hi_w3 headamp_himg_A]. apply Exists_cons_hd. cbn [hd_xv fst snd].
  unfold HQ_XO in Ha. lia. }
assert (H11v : getr regs2 11 = w64 (ans_rc (hq_exp rsegs cx r)))
  by (apply (he_at_reg _ _ _ _ 11 _ _ Hat); [he_in | reflexivity]).
rewrite H11v in Vst.
assert (Hm3 : he_mid fx2 ly3 S3 W3 regs3 mem3 md3).
{ split.
  { refine (he_base3_kept B MT errno_low cx r ev fx2 fx2 hq_shX hq_shX _ _ _ _ _ _ _ _ _ _ _ _ HS Hb Hcore3 _ _ Hfx).
    - intros a Ha Hn. apply Hmem3; [exact Ha|]. intros Hw. apply Hn. right. left. unfold HQ_XO in *. lia.
    - unfold hs_fsh_at in *. apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh).
      intros i Hi. rewrite hq_shX_len in Hi. apply Hmem3; [lia|].
      unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. unfold HQ_XO. lia. }
  split.
  { assert (Hat2 : hs_at_cx rsegs cx W2 mem2 regs2 (hq_L_seg rsegs cx ++ he_L)).
    { apply (he_at_sub _ _ _ _ _ Hat). intros f Hf. cbn [hq_L_seg hq_L_frame he_L app] in Hf.
      repeat (destruct Hf as [<-|Hf]; [he_in|]). destruct Hf. }
    unfold hs_at_cx, hs_at in *. apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ Hat2).
    intros f Hf. cbn [hq_L_seg hq_L_frame he_L app] in Hf.
    repeat (destruct Hf as [<-|Hf];
     [cbn [fst hm_keeps hd_xv];
      first [ apply (he_kr regs2 regs3 [1%bv; 10%bv; 11%bv; 12%bv]); [exact Hkr3 | lia | vm_compute; reflexivity]
            | let i := fresh "i" in let Hi := fresh "Hi" in
              intros i Hi; apply Hmem3; unfold HQ_XO, T_SEG_STK, ASTACK in *; lia ] | ]).
    destruct Hf. }
  split; [exact Hcor|].
  exact (he_x_store W2 W3 mem2 mem3 Hxat Vst Hmem3). }
change (mkCfg (mkst regs3 (w64 HE_CK_OBJECT) mem3 (seg_rom rsegs)) md3)
  with (@cfg_at fx2 rsegs A_CK_OBJECT regs3 mem3 md3).
destruct (he_site fx2 ly3 S3 W3 regs3 mem3 md3 RA_CK_OBJECT Hm3 H1 ltac:(unfold RA_CK_OBJECT; lia) eq_refl)
  as (HPre & Hown3 & HFa & Hsh & Hwf & Hcor3 & Hcap3 & Hres & Hxb).
destruct (headamp_A_site_object rsegs B _ _ _ _ _ _ _ _ _ _ regs3 ly3 S3 W3 mem3 md3 (x_e rsegs cx) (x_pos rsegs cx) r
  (hq_ans rsegs cx r) HPre Hown3 HFa Hsh Hwf Hcor3 Hcap3 eq_refl Hres Hxb)
  as (Hrcb & Vx & RAx & Ox & Ax & Hal & Hneg).
refine (hc_check_object_call (fx := fx2) rsegs B MT (CKO fx2) POST _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs3
  (e_R (x_e rsegs cx)) (ans_rc (hq_ans rsegs cx r)) (ans_rc (hq_ans rsegs cx r)) (e_F (x_e rsegs cx) + 0x180)
  (e_F (x_e rsegs cx) + 0x1a0) (he_hc_core B MT cx _ _ _ _ _ _ _ _ HP Hcore3) H1 _ _ _
  Hrcb Hrcb (iff_refl _) Vx RAx Ox Ax Hal Hneg _).
{ rewrite H10, <- Hrc. apply (he_at_reg _ _ _ _ 27 _ _ Hat); [he_in | reflexivity]. }
{ rewrite H11. apply (he_at_reg _ _ _ _ 26 _ _ Hat); [he_in | reflexivity]. }
{ rewrite H12. exact H18. }
intros W4 ly4 S4 regs4 mem4 md4 Hle4 Hcc4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hmem4.
assert (Hcore4 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly4 S4 W4 regs4 mem4 md4)
  by exact (he_core_call B MT MTL cx _ _ T_check_STK _ _ _ _ _ _ _ _ _ _ _ _ HP Hcore3
    ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) Hcc4 Hpres4 Hfr4 Hperm4 Hio4 Hmo4 Hmem4).
apply (he_from_obj_ret fx2 ly4 S4 W4 regs4 mem4 md4).
apply (he_mid_kept fx2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4
  (fun a => e_R (x_e rsegs cx) - T_check_STK <= a < e_R (x_e rsegs cx)) Hm3 Hcore4); [| exact Hmem4 |].
- intros a Ha. unfold T_check_STK, T_SEG_STK, ASTACK in *. lia.
- intros q Hq. apply Hpres4. unfold acallee_saved. unfold he_keep in Hq. cbn [In] in Hq. lia.
Qed.

(* ======================================= RC 0x83694: s2 := x, a1 := x->n ======================================= *)
Lemma he_from_RC : @hq_from_RC fx rc SK rsegs B MT cx r POST.
Proof.
unfold hq_from_RC. intros fx2 ly2 S2 W2 regs2 mem2 md2 (Hb & Hat & Hcor & Hrcn & Hxat).
pose proof HS as (HP & _).
destruct he_geo as (HF4 & HFc & HF32 & HFapp & HR & HR47 & Hs1 & Hs2 & Hc1 & Hcap & Hnull).
unfold T_SEG_STK, ASTACK in HR.
pose proof (@ASAN_CEIL_range rc) as [[Hc1' Hc2'] _]. unfold ASAN_CEIL in Hc1', Hc2'.
pose proof Hb as (Hcore & Hfx & Hfsh & _). pose proof Hcore as (HJ & _).
pose proof Hxat as (Hg & Hl & Hlc & _).
assert (H9 : getr regs2 9 = w64 (e_R (x_e rsegs cx))) by (apply (he_at_reg _ _ _ _ 9 _ _ Hat); [he_in | reflexivity]).
assert (Vx : val_mem rsegs (mrestrict (w_H W2) mem2) (e_R (x_e rsegs cx) + 0x108) 8 (e_F (x_e rsegs cx) + HQ_XO)).
{ pose proof (he_at_cell _ _ _ _ 0x108 _ Hat ltac:(he_in)) as V. rewrite Z.mod_small in V by (unfold HQ_XO; lia).
  exact V. }
assert (Vn : val_mem rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + HQ_XO + 0x7c) 4
  (Z.of_nat (length (ans_cells (hq_exp rsegs cx r))))).
{ pose proof (hd_garr8_le4 rsegs _ _ _ (he_x_n _ _ _ _ _ _ Hl Hg)) as V.
  unfold X_CELLS in Hl. rewrite Z.mod_small in V by lia. exact V. }
eapply SRr_bind.
{ refine (he_blk_rc (fx := fx2) B MT MTL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ regs2 (e_R (x_e rsegs cx))
    (e_F (x_e rsegs cx) + HQ_XO) _ HJ H9 _ _ _ _ _ Vx Vn); unfold HQ_XO, X_CELLS, T_SEG_STK, ASTACK in *; lia. }
intros W3 c3 Hle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr3 & Hfr3 & Hperm3 & Hio3 & Hmo3 & Hmem3 &
  (H18 & H11)).
assert (Hcore3 : hs_core rsegs B MT cx (hq_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
{ refine (he_core_blk B MT MTL cx _ (fun _ => False) [11%bv; 18%bv] _ _ _ _ _ _ _ _ _ _ _ _ Hcore HJ3
    Hkr3 _ Hfr3 Hperm3 Hio3 Hmo3 Hmem3 (fun a (H : False) => match H with end)). he_clob. }
apply (he_from_RCM fx2 ly3 S3 W3 regs3 mem3 md3).
split.
{ refine (he_base3_kept B MT errno_low cx r ev fx2 fx2 hq_shX hq_shX _ _ _ _ _ _ _ _ _ _ _ _ HS Hb Hcore3 _ _ Hfx).
  - intros a Ha _. exact (Hmem3 a Ha (fun H => H)).
  - unfold hs_fsh_at in *. apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh).
    intros i Hi. rewrite hq_shX_len in Hi. apply Hmem3; [lia | intros []]. }
split.
{ assert (Hat3 : hs_at_cx rsegs cx W3 mem3 regs3
    (hq_L_seg rsegs cx ++
     [(LCell XR 0x20, e_F (x_e rsegs cx)); (LCell XR 0x60, e_F (x_e rsegs cx)); (LCell XR 0xf0, e_pp (x_e rsegs cx));
      (LCell XR 0x108, e_F (x_e rsegs cx) + HQ_XO);
      (LCell XR 0x110, hd_xv (x_e rsegs cx) XProps); (LCell XR 0x118, 3 * e_cap (x_e rsegs cx) + 3)])).
  { unfold hs_at_cx, hs_at in *. apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ Hat).
    intros f Hf. cbn [hq_L_seg hq_L_frame app] in Hf.
    repeat (destruct Hf as [<-|Hf];
     [cbn [fst hm_keeps hd_xv];
      first [ apply (he_kr regs2 regs3 [11%bv; 18%bv]); [exact Hkr3 | lia | vm_compute; reflexivity]
            | let i := fresh "i" in let Hi := fresh "Hi" in
              intros i Hi; apply Hmem3; [lia | intros []] ] | ]).
    destruct Hf. }
  assert (H11' : getr regs3 (Z_to_bv 5 11) = w64 (ans_rc (hq_exp rsegs cx r)))
    by (rewrite (he_r5 11%bv 11 eq_refl), Hrcn; exact H11).
  assert (H18' : getr regs3 (Z_to_bv 5 18) = w64 (e_F (x_e rsegs cx) + HQ_XO))
    by (rewrite (he_r5 18%bv 18 eq_refl); exact H18).
  unfold hs_at_cx, hs_at in *. rewrite Forall_forall in Hat3 |- *. intros f Hf.
  cbn [hq_L_seg hq_L_frame app] in Hf.
  repeat (destruct Hf as [<-|Hf];
   [first [ exact H11' | exact H18' | apply Hat3; he_in ] | ]).
  destruct Hf. }
split; [exact Hcor|].
destruct Hxat as (_ & Hrest). split; [|exact Hrest].
apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
apply (hm_bytes_kept rsegs (w_H W2) mem2); [exact (proj2 (hm_bytes_zbytes rsegs _ _ _ _) Hg)|].
intros a Ha. rewrite (hq_x_open_len _ _ _ Hl) in Ha. unfold HQ_XO in Ha.
apply Hmem3; [lia | intros []].
Qed.

End p.

Theorem he_rc : @hq_piece_M3e_rc_stmt fx rc SK rsegs B MT.
Proof.
intros cx POST r ev HS HF. split; [exact (he_from_RC cx r POST ev HS HF) | exact (he_from_RCM cx r POST ev HS HF)].
Qed.

End d.
End b.

Print Assumptions he_rc.
About he_rc.
