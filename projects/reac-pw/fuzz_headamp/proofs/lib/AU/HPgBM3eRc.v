(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94; every address below is measured on the
   unstripped twin 1674e30a0698f381704e66d2398d7906c881f4ba8fc619cb41b89fb97ad112ff, whose loaded sections are
   byte-equal to the pin's except .note.gnu.build-id): the piece "x->rc and the last four checks" of the walk of LLVMFuzzerTestOneInput
   (0x80c40), lib/AU/HPgSegM.v hqu_piece_M3e_rc_stmt (RC 0x83850 and RCM 0x8385c -> FIRST 0x838e4). Proves no
   function (kind: segment lemma).

   THE WALK. From RC the run reads x (R+0x138), x->n and F (R+0x48) and joins RCM with a3 = x->n, which the RC cut
   says is expect_of's rc. From RCM it stores a3 into x->rc, so x holds expect_of's answer byte for byte
   (Spec/HeadBytes.v x_bytes), then calls check_object(rc, &res, &x), check_cells(out, rc, &x) and, for rc >= 0,
   check_keys(&res, &x) and check_refusal(&res, &x) (lib/AU/HPgBM3eRcBlk.v runs the straight-line code between
   the calls), and closes x's 17 shadow granules (lib/AU/HPgSteps.v hdu_scope_x_out) to reach FIRST with the
   frame's shadow back at the record's hi_shB. Each call goes through lib/A/HPgCalls.v hc_call_ck with its
   contract (lib/A/HPgCSpec.v) at image B's entry; lib/AU/HPgSiteB.v supplies the contract's premises from res
   (the parse's answer) and x (expect_of's), which are the same answer on an uncorrupted record. Between the cuts
   the walk carries br_inv: the cut base hqu_base3 with x in scope, the registers and real-frame cells FIRST and
   the calls read, and x's bytes.

   SECTION HYPOTHESES (the files that discharge them):
   - MTL : ameter_laws MT, errno_low : api_env rsegs B (as lib/AU/HPgBM3eBase.v);
   - CK_OBJ, CK_CELLS, CK_KEYS, CK_REF: the four check contracts of lib/A/HPgCSpec.v at image B's entries
     check_object 0x840c0, check_cells 0x841c0, check_keys 0x843a4, check_refusal 0x84438, for every float state
     (the image-B walks of the check functions). *)
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
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YK1e.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Model Layout Accessors Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgCalls HPgSiteA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgSeg HPgSegM HPgMem HPgSiteB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import HPgBM3eBase HPgBM3eRcBlk.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgSteps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* ======================================= x's bytes ======================================= *)
(* x->n, the word at x + 0x7c, while the pair loop's bytes are in x *)
Lemma br_x_n : forall {fx : YK11.FPState} H mem a cs keys rf, (length cs <= X_CELLS)%nat ->
garr8 rsegs (mrestrict H mem) a (hd_zbytes (hqu_x_open cs keys rf)) ->
val_mem rsegs (mrestrict H mem) (a + 0x7c) 4 (Z.of_nat (length cs)).
Proof.
intros fx H mem a cs keys rf Hl Hx.
apply (proj2 (hm_bytes_zbytes rsegs H mem a _)) in Hx.
unfold hqu_x_open in Hx.
rewrite app_assoc, app_assoc in Hx.
apply (proj1 (hm_bytes_app rsegs H mem a _ _)) in Hx as [_ Hx].
rewrite !length_app, repeat_length, length_x_cells_bytes, repeat_length in Hx.
unfold ha_res_bytes in Hx.
apply (proj1 (hm_bytes_app rsegs H mem _ _ _)) in Hx as [Hx _].
unfold Mem.le4 in Hx. apply hm_val_of_bytes in Hx.
unfold X_CELLS in Hl.
replace (a + Z.of_nat (4 + 12 * length cs + 12 * (X_CELLS - length cs))) with (a + 0x7c) in Hx
  by (unfold X_CELLS; lia).
rewrite Z_to_bv_unsigned in Hx. unfold bv_wrap in Hx. change (bv_modulus 64) with (2 ^ 64) in Hx.
rewrite Z.mod_small in Hx by lia. exact Hx.
Qed.

(* the store of rc into x->rc turns the pair loop's bytes into expect_of's answer *)
Lemma br_x_store : forall (o : answer),
(length (ans_cells o) <= X_CELLS)%nat -> ans_n o = Z.of_nat (length (ans_cells o)) ->
Model.overwrite (hqu_x_open (ans_cells o) (ans_keys o) (ans_rf o)) 0
  (Z_to_le_bytes 4 (bv_unsigned (Z_to_bv 64 (ans_rc o)) mod 2 ^ 32)) = x_bytes o.
Proof.
intros o Hl Hn. unfold Model.overwrite, hqu_x_open, x_bytes, ans_res_bytes.
rewrite length_Z_to_le_bytes. cbn [firstn app Nat.add].
change (repeat (Z_to_bv 8 0) 4 ++ ?l) with (Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: Z_to_bv 8 0 :: l).
cbn [skipn]. rewrite Hn. unfold Mem.le4 at 1.
change (2 ^ 32) with (2 ^ (8 * Z.of_nat 4)). rewrite YK1e.Z_to_le_bytes_mod. reflexivity.
Qed.

(* expect_of's null test, at a null flag of 0 or 1 *)
Lemma br_null_flag : forall z, 0 <= z <= 1 -> negb (z =? 0) = (z =? 1).
Proof. intros z Hz. destruct (Z.eq_dec z 0) as [->|H]; [reflexivity|]. assert (z = 1) as -> by lia. reflexivity. Qed.

Lemma br_shX : headamp_B_shX = hqu_shX.
Proof. reflexivity. Qed.

Lemma br_shX_out : hm_setn hqu_shX 88 17 248 = hi_shB headamp_himg_B.
Proof. vm_compute. reflexivity. Qed.

(* ======================================= the piece ======================================= *)
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis errno_low : api_env rsegs B.
Hypothesis CK_OBJ : forall fx' : YK11.FPState, @hd_check_object_specX fx' rc SK rsegs B MT BR_CK_OBJECT.
Hypothesis CK_CELLS : forall fx' : YK11.FPState, @hd_check_cells_specX fx' rc SK rsegs B MT BR_CK_CELLS.
Hypothesis CK_KEYS : forall fx' : YK11.FPState, @hd_check_keys_specX fx' rc SK rsegs B MT BR_CK_KEYS.
Hypothesis CK_REF : forall fx' : YK11.FPState, @hd_check_refusal_specX fx' rc SK rsegs B MT BR_CK_REFUSAL.

(* the registers and real-frame cells the walk keeps from RCM to FIRST *)
Definition br_L (cx : hsu_scx rsegs) : list (hd_loc * Z) :=
  hqu_L_seg rsegs cx ++
  [(LReg 18, e_F (x_e rsegs cx) + HQU_XO); (LReg 21, e_F (x_e rsegs cx));
   (LCell XR 0x18, e_F (x_e rsegs cx)); (LCell XR 0x48, e_F (x_e rsegs cx));
   (LCell XR 0x140, hd_xv (x_e rsegs cx) XProps); (LCell XR 0x148, e_pp (x_e rsegs cx));
   (LCell XR 0x150, 3 * e_cap (x_e rsegs cx) + 3); (LCell XR 0x158, e_pod (x_e rsegs cx))].

(* what the walk carries between the calls *)
Definition br_inv (cx : hsu_scx rsegs) (r : Model.pod_rec) (fx2 : YK11.FPState) ly2 S2 W2 regs2 mem2 md2 : Prop :=
  @hqu_base3 fx rc SK rsegs B MT cx fx2 r hqu_shX ly2 S2 W2 regs2 mem2 md2 /\
  hsu_at_cx rsegs cx W2 mem2 regs2 (br_L cx) /\
  garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + HQU_XO) (hd_zbytes (x_bytes (hqu_exp rsegs cx r))) /\
  Model.corrupt r = false.

(* the facts of the segment's start every step reads *)
Lemma br_start : forall cx r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev ->
hsu_pre rsegs B headamp_himg_B cx (hi_shA headamp_himg_B) /\ Model.pod_rec_wf r /\
In (4, x_pos rsegs cx) (x_own rsegs cx) /\ e_F (x_e rsegs cx) = frame_addr (x_lyc rsegs cx) 4 (x_pos rsegs cx) /\
e_F (x_e rsegs cx) mod 32 = 0 /\ 4096 <= e_F (x_e rsegs cx) /\ e_F (x_e rsegs cx) + 1024 <= alloc_ceiling /\
alloc_ceiling + T_SEG_STK <= e_R (x_e rsegs cx) /\ e_R (x_e rsegs cx) <= 2 ^ 47 /\
0 <= e_cap (x_e rsegs cx) <= 9 /\ 0 <= e_null (x_e rsegs cx) <= 1 /\
In (e_out (x_e rsegs cx), 3 * (e_cap (x_e rsegs cx) + 1)) (ablocks B (x_lyc rsegs cx) (x_Sc rsegs cx)) /\
e_rc (x_e rsegs cx) = ans_rc (hqu_ans rsegs cx r) /\ - 1 <= e_rc (x_e rsegs cx) <= 9 /\
0x7fff8000 <= shadow_addr (e_F (x_e rsegs cx)) /\ shadow_addr (e_F (x_e rsegs cx)) + 128 <= 0x10007fef8080 /\
alloc_ceiling < 2 ^ 47.
Proof.
intros cx r ev HS.
pose proof HS as (HP & _ & Hwf & _ & _ & _ & _ & _ & _ & _ & _ & Houtb & _ & _ & Hrc & _).
destruct (hbe_seg B cx _ HP) as (_ & Hown & HF & H32 & H4k & Hceil & _ & _ & HR1 & HR2 & _ & Hcap & Hnull).
destruct Houtb as (_ & Houtin & _).
pose proof (hbe_fsh_rng B cx _ HP) as (Hs1 & Hs2).
pose proof (@YM05.alloc_ceiling_lt rc) as Hc47.
assert (Hrcb : -1 <= e_rc (x_e rsegs cx) <= 9).
{ rewrite Hrc. unfold hqu_ans.
  pose proof (parse_props_total (hd_props (e_null (x_e rsegs cx)) (Model.buf r)) (e_cap (x_e rsegs cx)) ltac:(lia)) as Hok.
  apply answer_ok_parts in Hok as (Hcase & _). destruct Hcase as [(H1 & _)|(H1 & _)]; lia. }
split; [exact HP|]. split; [exact Hwf|]. split; [exact Hown|]. split; [exact HF|]. split; [exact H32|].
split; [exact H4k|]. split; [exact Hceil|]. split; [exact HR1|]. split; [exact HR2|]. split; [exact Hcap|].
split; [exact Hnull|]. split; [exact Houtin|]. split; [exact Hrc|]. split; [exact Hrcb|].
split; [exact Hs1|]. split; [exact Hs2 | exact Hc47].
Qed.

(* expect_of's cells fit in x *)
Lemma br_exp_len : forall cx r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev -> Model.corrupt r = false ->
(length (ans_cells (hqu_exp rsegs cx r)) <= X_CELLS)%nat /\ length (x_bytes (hqu_exp rsegs cx r)) = 136%nat /\
hqu_ans rsegs cx r = hqu_exp rsegs cx r.
Proof.
intros cx r ev HS Hcor. destruct (br_start cx r ev HS) as (_ & Hwf & _ & _ & _ & _ & _ & _ & _ & Hcap & Hnull & _).
pose proof (hbe_ans_exp cx r Hwf Hcor Hnull) as E.
pose proof (hbe_ans_ok cx r Hcap) as (_ & Hl & _). rewrite E in Hl.
split; [exact Hl|]. split; [exact (length_x_bytes _ Hl) | exact E].
Qed.

(* x's place: inside F, below the ceiling and the real frame *)
Lemma br_x_geo : forall cx r ev, @hqu_start_M03 fx rc SK rsegs B cx r ev ->
0 <= e_F (x_e rsegs cx) + HQU_XO /\ e_F (x_e rsegs cx) + HQU_XO + 136 <= e_F (x_e rsegs cx) + 1024 /\
e_F (x_e rsegs cx) + HQU_XO + 136 < e_R (x_e rsegs cx) - T_SEG_STK /\ (e_F (x_e rsegs cx) + HQU_XO) mod 4 = 0.
Proof.
intros cx r ev HS. destruct (br_start cx r ev HS) as (_ & _ & _ & _ & H32 & H4k & Hc & HR & _).
unfold HQU_XO. split; [lia|]. split; [lia|]. split; [lia|].
pose proof (Z.div_mod (e_F (x_e rsegs cx)) 32 ltac:(lia)) as Hd.
symmetry. apply (Z.mod_unique _ 4 (8 * (e_F (x_e rsegs cx) / 32) + 0xb0) 0); [left; lia | lia].
Qed.

(* ---------------- carrying br_inv across a check call ---------------- *)
Lemma br_inv_call : forall cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
br_inv cx r fx2 ly2 S2 W2 regs2 mem2 md2 ->
hc_core rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) (x_k rsegs cx)
  ly3 S3 W3 mem3 md3 regs3 (e_R (x_e rsegs cx)) ->
aregs_preserved regs2 regs3 -> frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) ->
same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall y, 0 <= y < 2 ^ 64 -> ~ (e_R (x_e rsegs cx) - T_check_STK <= y < e_R (x_e rsegs cx)) ->
 aview rsegs (w_H W3) mem3 y = aview rsegs (w_H W2) mem2 y) ->
br_inv cx r fx2 ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HS Hinv HC3 Hpres Hfr Hperm Hio Hmo Hkeep.
destruct Hinv as (Hb & Hat & Hx & Hcor).
destruct (br_start cx r ev HS) as (HP & _ & _ & _ & _ & HF4 & HFc & HR & HR47 & _ & _ & _ & _ & _ & Hs1 & Hs2 & Hc47).
pose proof (br_x_geo cx r ev HS) as (Hx0 & Hx1 & Hx2 & _).
destruct (br_exp_len cx r ev HS Hcor) as (_ & Hxl & _).
assert (Hcore3 : hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
{ pose proof Hb as (Hcore & _).
  apply (hbe_core_call B MT MTL cx _ (hqu_E3 rsegs B cx) T_check_STK ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
    HP Hcore ltac:(unfold T_check_STK, T_SEG_STK, ASTACK; lia) HC3 Hpres Hfr Hperm Hio Hmo Hkeep). }
assert (Hk : forall a, 0 <= a < 2 ^ 64 -> ~ hbe_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hw. apply Hkeep; [exact Ha|]. intros Hs. apply Hw. left. unfold T_check_STK, T_SEG_STK, ASTACK in *. lia. }
pose proof Hb as (_ & Hfxk & Hfsh & _).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
split.
{ apply (hbe_base3_kept B MT errno_low cx r ev fx2 fx2 hqu_shX hqu_shX ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
    HS Hb Hcore3 Hk); [|exact Hfxk].
  unfold hsu_fsh_at in *. apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh).
  intros i Hi. rewrite hqu_shX_len in Hi. change (Z.of_nat 116) with 116 in Hi. apply Hkeep; [lia|].
  unfold T_check_STK, T_SEG_STK, ASTACK in *. lia. }
split.
{ unfold hsu_at_cx, hsu_at in *. apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ Hat).
  intros f Hf. unfold br_L, hqu_L_seg, hqu_L_frame in Hf. cbn [app In] in Hf.
  unfold T_check_STK, T_SEG_STK, ASTACK in *.
  repeat (destruct Hf as [<-|Hf];
    [ cbn [hm_keeps fst hd_xv];
      first [ apply Hpres; unfold acallee_saved; lia
            | intros i Hi; apply Hkeep; lia ] |]).
  destruct Hf. }
split.
{ apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
  apply (hm_bytes_kept rsegs _ _ _ _ _ _ (proj2 (hm_bytes_zbytes rsegs _ _ _ _) Hx)).
  intros y Hy. rewrite Hxl in Hy. change (Z.of_nat 136) with 136 in Hy.
  apply Hkeep; [lia|]. unfold T_check_STK, T_SEG_STK, ASTACK in *. lia. }
exact Hcor.
Qed.

(* ---------------- carrying br_inv across a straight-line block that writes nothing ---------------- *)
Definition br_clob_ok (clob : list (bv 5)) : bool :=
  forallb (fun c => (bv_unsigned c =? 1) || ((10 <=? bv_unsigned c) && (bv_unsigned c <=? 17))) clob.

Lemma br_notin : forall (clob : list (bv 5)) (q : Z), br_clob_ok clob = true ->
0 <= q < 32 -> q <> 1 -> ~ (10 <= q <= 17) -> ~ In (Z_to_bv 5 q) clob.
Proof.
intros clob q Hc Hq H1 H2 Hin. unfold br_clob_ok in Hc. rewrite forallb_forall in Hc.
specialize (Hc _ Hin). rewrite Z_to_bv_unsigned in Hc. unfold bv_wrap in Hc. change (bv_modulus 5) with 32 in Hc.
rewrite Z.mod_small in Hc by lia.
apply orb_true_iff in Hc as [Hc|Hc]; [apply Z.eqb_eq in Hc; lia|].
apply andb_true_iff in Hc as [Ha Hb]. apply Z.leb_le in Ha. apply Z.leb_le in Hb. lia.
Qed.

Lemma br_not_in_bv : forall (q : Z) (clob : list (bv 5)), 0 <= q < 32 ->
forallb (fun c => negb (bv_unsigned c =? q)) clob = true -> ~ In (Z_to_bv 5 q) clob.
Proof.
intros q clob Hq H Hin. rewrite forallb_forall in H. specialize (H _ Hin).
rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 5) with 32 in H.
rewrite Z.mod_small in H by lia. rewrite Z.eqb_refl in H. discriminate H.
Qed.

Lemma br_reg_kept : forall (regs2 regs3 : bvmap 5 word) (clob : list (bv 5)) q,
(forall r0 : bv 5, bv_unsigned r0 <> 0 -> ~ In r0 clob -> getr regs3 r0 = getr regs2 r0) ->
0 < q < 32 -> forallb (fun c => negb (bv_unsigned c =? q)) clob = true ->
getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q).
Proof.
intros regs2 regs3 clob q Hkr Hq Hc. apply Hkr.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. lia.
- apply br_not_in_bv; [lia | exact Hc].
Qed.

Lemma br_inv_blk : forall cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 (clob : list (bv 5)),
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
br_inv cx r fx2 ly2 S2 W2 regs2 mem2 md2 ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly3 S3 W3 mem3 md3 (x_k rsegs cx) ->
(forall q : bv 5, bv_unsigned q <> 0 -> ~ In q clob -> getr regs3 q = getr regs2 q) ->
br_clob_ok clob = true ->
frames S3 = frames S2 -> Permutation (ablocks B ly3 S3) (ablocks B ly2 S2) -> same_io md2 md3 -> mo_le MT S2 S3 0 ->
(forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a) ->
br_inv cx r fx2 ly3 S3 W3 regs3 mem3 md3.
Proof.
intros cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 clob HS Hinv HJ3 Hkr Hcl Hfr Hperm Hio Hmo Hkeep.
destruct Hinv as (Hb & Hat & Hx & Hcor).
destruct (br_exp_len cx r ev HS Hcor) as (_ & Hxl & _).
pose proof Hb as (Hcore & Hfxk & Hfsh & _).
assert (Hreg : forall q, 0 <= q < 32 -> q <> 0 -> q <> 1 -> ~ (10 <= q <= 17) ->
  getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q)).
{ intros q Hq H0 H1 H2. apply Hkr; [|exact (br_notin clob q Hcl Hq H1 H2)].
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 5) with 32. rewrite Z.mod_small by lia. exact H0. }
assert (Hcore3 : hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
{ apply (hbe_core_blk B MT MTL cx (hqu_E3 rsegs B cx) (fun _ => False) clob ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
    Hcore HJ3 Hkr); [| exact Hfr | exact Hperm | exact Hio | exact Hmo | intros a Ha _; exact (Hkeep a Ha) | intros a []].
  intros q Hq. apply (br_notin clob q Hcl); lia. }
split.
{ apply (hbe_base3_kept B MT errno_low cx r ev fx2 fx2 hqu_shX hqu_shX ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
    HS Hb Hcore3 (fun a Ha _ => Hkeep a Ha)); [|exact Hfxk].
  unfold hsu_fsh_at in *. apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh).
  intros i Hi. apply Hkeep. destruct (br_start cx r ev HS) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hs1 & Hs2 & _).
  rewrite hqu_shX_len in Hi. change (Z.of_nat 116) with 116 in Hi. lia. }
split.
{ unfold hsu_at_cx, hsu_at in *. apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ Hat).
  destruct (br_start cx r ev HS) as (_ & _ & _ & _ & _ & _ & _ & HR & HR47 & _).
  pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
  unfold T_SEG_STK, ASTACK in *.
  intros f Hf. unfold br_L, hqu_L_seg, hqu_L_frame in Hf. cbn [app In] in Hf.
  repeat (destruct Hf as [<-|Hf];
    [ cbn [hm_keeps fst hd_xv];
      first [ apply Hreg; lia
            | intros i Hi; apply Hkeep; lia ] |]).
  destruct Hf. }
split.
{ apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
  apply (hm_bytes_kept rsegs _ _ _ _ _ _ (proj2 (hm_bytes_zbytes rsegs _ _ _ _) Hx)).
  intros y Hy. rewrite Hxl in Hy. change (Z.of_nat 136) with 136 in Hy.
  pose proof (br_x_geo cx r ev HS) as (Hx0 & Hx1 & Hx2 & _).
  destruct (br_start cx r ev HS) as (_ & _ & _ & _ & _ & _ & _ & HR & HR47 & _).
  apply Hkeep. unfold T_SEG_STK, ASTACK in *. lia. }
exact Hcor.
Qed.

(* the frame for locals at the layout of any state of the journal *)
Lemma br_frame_at : forall cx r ev ly2 S2 W2 mem2 md2,
@hqu_start_M03 fx rc SK rsegs B cx r ev ->
ajournal rsegs B (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx)
  (x_W0 rsegs cx) (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem2 md2 (x_k rsegs cx) ->
e_F (x_e rsegs cx) = frame_addr ly2 4 (x_pos rsegs cx).
Proof.
intros cx r ev ly2 S2 W2 mem2 md2 HS HJ.
destruct (br_start cx r ev HS) as (HP & _ & _ & HF & _).
pose proof HP as (HJ0 & _).
rewrite HF.
rewrite (hc_frame_addr_j rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 (x_pos rsegs cx) HJ0).
rewrite (hc_frame_addr_j rsegs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 4 (x_pos rsegs cx) HJ).
reflexivity.
Qed.

(* ---------------- 0x838a0: x out of scope, then FIRST ---------------- *)
Lemma br_xout : forall cx r ev POST fx2 ly2 S2 W2 regs2 mem2 md2,
@hqu_start_M03 fx rc SK rsegs B cx r ev -> @hqu_from_FIRST fx rc SK rsegs B MT cx r POST ->
br_inv cx r fx2 ly2 S2 W2 regs2 mem2 md2 -> getr regs2 10 = w64 (-8) ->
SRr rsegs W2 (@cfg_at fx2 rsegs BR_XOUT regs2 mem2 md2) POST.
Proof.
intros cx r ev POST fx2 ly2 S2 W2 regs2 mem2 md2 HS HF Hinv H10.
destruct (br_start cx r ev HS) as (HP & Hwf & Hown & HF0 & H32 & H4k & Hc & HR & HR47 & Hcap & Hnull & Hout & Hrc
  & Hrcb & Hs1 & Hs2 & Hc47).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
pose proof Hinv as (Hb & Hat & Hx & Hcor).
pose proof Hb as (Hcore & Hfxk & Hfsh & _).
pose proof Hcore as (HJ & _).
pose proof (br_frame_at cx r ev ly2 S2 W2 mem2 md2 HS HJ) as HFa.
pose proof (hbe_at_get _ _ _ _ _ 19 (shadow_addr (e_F (x_e rsegs cx))) Hat
  ltac:(unfold br_L, hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as H19.
rewrite HFa in H19.
pose proof (AR_laws_ok rsegs B) as LAWS.
eapply SRr_bind.
{ apply (@HPgSteps.hdu_scope_x_out fx2 rc SK B MT MTL LAWS
    (x_STK rsegs cx) (x_sp0 rsegs cx) (x_FP rsegs cx) (x_ly rsegs cx) (x_S rsegs cx) (x_W0 rsegs cx)
    (x_mem0 rsegs cx) (x_md0 rsegs cx) (x_own rsegs cx) ly2 S2 W2 mem2 md2 (x_k rsegs cx) regs2 4 (x_pos rsegs cx)
    HJ Hown ltac:(lia) H19 H10); [rewrite <- HFa; lia | rewrite <- HFa; lia | change (fs_frame_bytes 4 / 8) with 128; lia]. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr & Hfr & Hperm & Hio & Hmo & Hkeep & HV).
rewrite <- HFa in Hkeep, HV.
assert (Hk : forall a, 0 <= a < 2 ^ 64 -> ~ hbe_wz cx a -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a).
{ intros a Ha Hw. apply Hkeep; [exact Ha|]. intros Hs. apply Hw. right. right. lia. }
assert (Hcore3 : hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
{ apply (hbe_core_blk B MT MTL cx (hqu_E3 rsegs B cx)
    (fun a => shadow_addr (e_F (x_e rsegs cx)) + 88 <= a < shadow_addr (e_F (x_e rsegs cx)) + 105) []
    ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hcore HJ3 Hkr);
  [ intros q _ []
  | exact Hfr | exact Hperm | exact Hio | exact Hmo | exact Hkeep
  | intros a Ha; apply (hbe_wz_E3 B cx a); right; exact Ha ]. }
apply (HF fx2 ly3 S3 W3 regs3 mem3 md3).
split.
{ apply (hbe_base3_kept B MT errno_low cx r ev fx2 fx2 hqu_shX (hi_shB headamp_himg_B)
    ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HS Hb Hcore3 Hk); [|exact Hfxk].
  unfold hsu_fsh_at in *. rewrite <- br_shX_out.
  apply (hm_fsh_set rsegs _ _ _ _ _ _ 88 17 248 Hfsh).
  - intros i Hi. change (Z.of_nat 88) with 88 in Hi. change (Z.of_nat (88 + 17)) with 105 in Hi.
    rewrite (HV i ltac:(lia)). reflexivity.
  - intros i Hi Hn. rewrite hqu_shX_len in Hi. change (Z.of_nat 116) with 116 in Hi.
    change (Z.of_nat 88) with 88 in Hn. change (Z.of_nat (88 + 17)) with 105 in Hn.
    apply Hkeep; lia. }
unfold hsu_at_cx, hsu_at in *.
assert (Hat3 : Forall (fun f => hd_at rsegs (w_H W3) mem3 regs3 (x_e rsegs cx) (fst f) (snd f)) (br_L cx)).
{ apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ Hat).
  unfold T_SEG_STK, ASTACK in *.
  intros f Hf. unfold br_L, hqu_L_seg, hqu_L_frame in Hf. cbn [app In] in Hf.
  repeat (destruct Hf as [<-|Hf];
    [ cbn [hm_keeps fst hd_xv];
      first [ apply Hkr; [vm_compute; congruence | intros []]
            | intros i Hi; apply Hkeep; lia ] |]).
  destruct Hf. }
apply (hbe_at_sub _ _ _ _ _ _ Hat3).
intros y Hy. unfold br_L, hqu_L_seg, hqu_L_frame in *. cbn [In app] in Hy |- *.
repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy.
Qed.

(* the hypotheses every call's continuation hands over, in the order of HPgCalls.hc_call_ck *)
Ltac br_cont :=
  let W3 := fresh "W3" in let ly3 := fresh "ly3" in let S3 := fresh "S3" in let regs3 := fresh "regs3" in
  let mem3 := fresh "mem3" in let md3 := fresh "md3" in
  intros W3 ly3 S3 regs3 mem3 md3 ? ?HC3 ?Hpres ?Hfr ?Hperm ?Hio ?Hmo ?Hkeep.

(* ---------------- 0x84438: check_refusal(&res, &x), then 0x8389c, then 0x838a0 ---------------- *)
Lemma br_ref : forall cx r ev POST fx2 ly2 S2 W2 regs2 mem2 md2,
@hqu_start_M03 fx rc SK rsegs B cx r ev -> @hqu_from_FIRST fx rc SK rsegs B MT cx r POST ->
br_inv cx r fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 1 = w64 BR_REF_RET -> getr regs2 10 = w64 (e_F (x_e rsegs cx) + HQU_RES) ->
getr regs2 11 = w64 (e_F (x_e rsegs cx) + HQU_XO) ->
SRr rsegs W2 (@cfg_at fx2 rsegs BR_CK_REFUSAL regs2 mem2 md2) POST.
Proof.
intros cx r ev POST fx2 ly2 S2 W2 regs2 mem2 md2 HS HF Hinv Hra H10 H11.
destruct (br_start cx r ev HS) as (HP & Hwf & Hown & HF0 & H32 & H4k & Hc & HR & HR47 & Hcap & Hnull & Hout & Hrc
  & Hrcb & Hs1 & Hs2 & Hc47).
pose proof Hinv as (Hb & Hat & Hx & Hcor).
pose proof Hb as (Hcore & Hfxk & Hfsh & _ & _ & _ & _ & Hres & _).
pose proof Hcore as (HJ & _).
pose proof (br_frame_at cx r ev ly2 S2 W2 mem2 md2 HS HJ) as HFa.
pose proof (hbe_hc_core B MT cx _ _ ly2 S2 W2 regs2 mem2 md2 HP Hcore) as HC.
eapply (@hc_call_ck fx2 rc SK rsegs B MT BR_CK_REFUSAL BR_REF_RET POST); [exact HC | exact Hra | unfold BR_REF_RET; lia | reflexivity | |].
- intros HPre.
  assert (Hx' : garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x2c0)
    (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null (x_e rsegs cx) =? 0)) (e_cap (x_e rsegs cx)) r))))
    by (rewrite (br_null_flag _ Hnull); exact Hx).
  assert (Hfsh' : hd_fsh rsegs (w_H W2) mem2 (e_F (x_e rsegs cx)) headamp_B_shX) by (rewrite br_shX; exact Hfsh).
  destruct (headamp_B_site_refusal rsegs B _ _ _ _ _ _ _ _ _ _ regs2 ly2 S2 W2 mem2 md2 (x_e rsegs cx) (x_pos rsegs cx)
    r (hqu_ans rsegs cx r) HPre Hown HFa Hfsh' Hwf Hcor Hcap eq_refl Hres Hx')
    as (R4 & X4 & RV & XV & RA & XA & RO & XO & RP & XP & Hap).
  eapply (CK_REF fx2); [exact HPre | exact H10 | exact H11 | exact R4 | exact X4 | exact RV | exact XV
    | exact RA | exact XA | exact RO | exact XO | exact RP | exact XP | exact Hap].
- br_cont.
  pose proof (br_inv_call cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HS Hinv HC3 Hpres Hfr Hperm Hio Hmo
    Hkeep) as Hinv3.
  pose proof Hinv3 as ((Hcore3 & _) & _).
  pose proof Hcore3 as (HJ3 & _).
  eapply SRr_bind; [apply (@br_blk_li fx2 rc SK B MT MTL _ _ _ _ _ _ _ _ _ ly3 S3 W3 mem3 md3 (x_k rsegs cx) regs3 HJ3)|].
  intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & Hkr4 & Hfr4 & Hperm4 & Hio4 & Hmo4 & Hkeep4 & H10').
  apply (br_xout cx r ev POST fx2 ly4 S4 W4 regs4 mem4 md4 HS HF); [|exact H10'].
  apply (br_inv_blk cx r ev fx2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 [10]%bv HS Hinv3 HJ4 Hkr4
    eq_refl Hfr4 Hperm4 Hio4 Hmo4).
  intros a Ha. apply Hkeep4; [exact Ha | intros []].
Qed.

(* ---------------- 0x843a4: check_keys(&res, &x), then 0x83890 .. check_refusal ---------------- *)
Lemma br_keys : forall cx r ev POST fx2 ly2 S2 W2 regs2 mem2 md2,
@hqu_start_M03 fx rc SK rsegs B cx r ev -> @hqu_from_FIRST fx rc SK rsegs B MT cx r POST ->
br_inv cx r fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 1 = w64 BR_KEYS_RET -> getr regs2 10 = w64 (e_F (x_e rsegs cx) + HQU_RES) ->
getr regs2 11 = w64 (e_F (x_e rsegs cx) + HQU_XO) ->
SRr rsegs W2 (@cfg_at fx2 rsegs BR_CK_KEYS regs2 mem2 md2) POST.
Proof.
intros cx r ev POST fx2 ly2 S2 W2 regs2 mem2 md2 HS HF Hinv Hra H10 H11.
destruct (br_start cx r ev HS) as (HP & Hwf & Hown & HF0 & H32 & H4k & Hc & HR & HR47 & Hcap & Hnull & Hout & Hrc
  & Hrcb & Hs1 & Hs2 & Hc47).
pose proof Hinv as (Hb & Hat & Hx & Hcor).
pose proof Hb as (Hcore & Hfxk & Hfsh & _ & _ & _ & _ & Hres & _).
pose proof Hcore as (HJ & _).
pose proof (br_frame_at cx r ev ly2 S2 W2 mem2 md2 HS HJ) as HFa.
pose proof (hbe_hc_core B MT cx _ _ ly2 S2 W2 regs2 mem2 md2 HP Hcore) as HC.
eapply (@hc_call_ck fx2 rc SK rsegs B MT BR_CK_KEYS BR_KEYS_RET POST); [exact HC | exact Hra | unfold BR_KEYS_RET; lia | reflexivity | |].
- intros HPre.
  assert (Hx' : garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x2c0)
    (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null (x_e rsegs cx) =? 0)) (e_cap (x_e rsegs cx)) r))))
    by (rewrite (br_null_flag _ Hnull); exact Hx).
  assert (Hfsh' : hd_fsh rsegs (w_H W2) mem2 (e_F (x_e rsegs cx)) headamp_B_shX) by (rewrite br_shX; exact Hfsh).
  destruct (headamp_B_site_keys rsegs B _ _ _ _ _ _ _ _ _ _ regs2 ly2 S2 W2 mem2 md2 (x_e rsegs cx) (x_pos rsegs cx)
    r (hqu_ans rsegs cx r) HPre Hown HFa Hfsh' Hwf Hcor Hcap eq_refl Hres Hx')
    as (R4 & X4 & RV & XV & RA & XA & RO & XO & RP & XP & Hap).
  eapply (CK_KEYS fx2); [exact HPre | exact H10 | exact H11 | exact R4 | exact X4 | exact RV | exact XV
    | exact RA | exact XA | exact RO | exact XO | exact RP | exact XP | exact Hap].
- br_cont.
  pose proof (br_inv_call cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HS Hinv HC3 Hpres Hfr Hperm Hio Hmo
    Hkeep) as Hinv3.
  pose proof Hinv3 as ((Hcore3 & _) & Hat3 & _).
  pose proof Hcore3 as (HJ3 & _).
  eapply SRr_bind; [apply (@br_blk_keys_ret fx2 rc SK B MT MTL _ _ _ _ _ _ _ _ _ ly3 S3 W3 mem3 md3 (x_k rsegs cx) regs3 HJ3)|].
  intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & Hkr4 & Hfr4 & Hperm4 & Hio4 & Hmo4 & Hkeep4 & (Q1 & Q10 & Q11)).
  pose proof (hbe_at_get _ _ _ _ _ 26 (e_F (x_e rsegs cx) + HQU_RES) Hat3
    ltac:(unfold br_L, hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R26.
  pose proof (hbe_at_get _ _ _ _ _ 18 (e_F (x_e rsegs cx) + HQU_XO) Hat3
    ltac:(unfold br_L, hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R18.
  apply (br_ref cx r ev POST fx2 ly4 S4 W4 regs4 mem4 md4 HS HF).
  + apply (br_inv_blk cx r ev fx2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 [1; 10; 11]%bv HS Hinv3 HJ4 Hkr4
      eq_refl Hfr4 Hperm4 Hio4 Hmo4).
    intros a Ha. apply Hkeep4; [exact Ha | intros []].
  + exact Q1.
  + rewrite Q10. exact R26.
  + rewrite Q11. exact R18.
Qed.

(* ---------------- 0x841c0: check_cells(out, rc, &x), then the bltz at 0x83880 ---------------- *)
Lemma br_cells : forall cx r ev POST fx2 ly2 S2 W2 regs2 mem2 md2,
@hqu_start_M03 fx rc SK rsegs B cx r ev -> @hqu_from_FIRST fx rc SK rsegs B MT cx r POST ->
br_inv cx r fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 1 = w64 BR_CELLS_RET -> getr regs2 10 = w64 (e_out (x_e rsegs cx)) ->
getr regs2 11 = w64 (e_rc (x_e rsegs cx)) -> getr regs2 12 = w64 (e_F (x_e rsegs cx) + HQU_XO) ->
SRr rsegs W2 (@cfg_at fx2 rsegs BR_CK_CELLS regs2 mem2 md2) POST.
Proof.
intros cx r ev POST fx2 ly2 S2 W2 regs2 mem2 md2 HS HF Hinv Hra H10 H11 H12.
destruct (br_start cx r ev HS) as (HP & Hwf & Hown & HF0 & H32 & H4k & Hc & HR & HR47 & Hcap & Hnull & Hout & Hrc
  & Hrcb & Hs1 & Hs2 & Hc47).
pose proof Hinv as (Hb & Hat & Hx & Hcor).
pose proof Hb as (Hcore & Hfxk & Hfsh & _ & _ & _ & Hob & _ & _).
pose proof Hcore as (HJ & _ & _ & Hperm0 & _).
pose proof (br_frame_at cx r ev ly2 S2 W2 mem2 md2 HS HJ) as HFa.
pose proof (hbe_hc_core B MT cx _ _ ly2 S2 W2 regs2 mem2 md2 HP Hcore) as HC.
assert (Hout2 : In (e_out (x_e rsegs cx), 3 * (e_cap (x_e rsegs cx) + 1)) (ablocks B ly2 S2))
  by (apply (Permutation_in _ (Permutation_sym Hperm0)); exact Hout).
eapply (@hc_call_ck fx2 rc SK rsegs B MT BR_CK_CELLS BR_CELLS_RET POST); [exact HC | exact Hra | unfold BR_CELLS_RET; lia | reflexivity | |].
- intros HPre.
  assert (Hx' : garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x2c0)
    (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null (x_e rsegs cx) =? 0)) (e_cap (x_e rsegs cx)) r))))
    by (rewrite (br_null_flag _ Hnull); exact Hx).
  assert (Hfsh' : hd_fsh rsegs (w_H W2) mem2 (e_F (x_e rsegs cx)) headamp_B_shX) by (rewrite br_shX; exact Hfsh).
  destruct (headamp_B_site_cells rsegs B _ _ _ _ _ _ _ _ _ _ regs2 ly2 S2 W2 mem2 md2 (x_e rsegs cx) (x_pos rsegs cx)
    r (hqu_ans rsegs cx r) HPre Hown HFa Hfsh' Hout2 Hwf Hcor Hcap eq_refl Hob Hx')
    as (Hrb & XV & XA & XO & XP & X4 & Hpos).
  rewrite Hrc in H11.
  eapply (CK_CELLS fx2); [exact HPre | exact H10 | exact H11 | exact H12 | exact Hrb | exact XV | exact XA | exact XO
    | exact XP | exact X4 | exact Hpos].
- br_cont.
  pose proof (br_inv_call cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HS Hinv HC3 Hpres Hfr Hperm Hio Hmo
    Hkeep) as Hinv3.
  pose proof Hinv3 as ((Hcore3 & _) & Hat3 & _).
  pose proof Hcore3 as (HJ3 & _).
  pose proof (hbe_at_get _ _ _ _ _ 25 (e_rc (x_e rsegs cx)) Hat3
    ltac:(unfold br_L, hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R25.
  eapply SRr_bind; [apply (@br_blk_cells_ret fx2 rc SK B MT MTL _ _ _ _ _ _ _ _ _ ly3 S3 W3 mem3 md3 (x_k rsegs cx) regs3
    (e_rc (x_e rsegs cx)) HJ3 R25 ltac:(lia))|].
  intros W4 c4 _ [(Hlt & ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & Hkr4 & Hfr4 & Hperm4 & Hio4 & Hmo4 & Hkeep4 & H10')
                 |(Hge & ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & Hkr4 & Hfr4 & Hperm4 & Hio4 & Hmo4 & Hkeep4 & (Q1 & Q10 & Q11))].
  + apply (br_xout cx r ev POST fx2 ly4 S4 W4 regs4 mem4 md4 HS HF); [|exact H10'].
    apply (br_inv_blk cx r ev fx2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 [10]%bv HS Hinv3 HJ4 Hkr4
      eq_refl Hfr4 Hperm4 Hio4 Hmo4).
    intros a Ha. apply Hkeep4; [exact Ha | intros []].
  + pose proof (hbe_at_get _ _ _ _ _ 26 (e_F (x_e rsegs cx) + HQU_RES) Hat3
      ltac:(unfold br_L, hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R26.
    pose proof (hbe_at_get _ _ _ _ _ 18 (e_F (x_e rsegs cx) + HQU_XO) Hat3
      ltac:(unfold br_L, hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R18.
    apply (br_keys cx r ev POST fx2 ly4 S4 W4 regs4 mem4 md4 HS HF).
    * apply (br_inv_blk cx r ev fx2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 [1; 10; 11]%bv HS Hinv3 HJ4 Hkr4
        eq_refl Hfr4 Hperm4 Hio4 Hmo4).
      intros a Ha. apply Hkeep4; [exact Ha | intros []].
    * exact Q1.
    * rewrite Q10. exact R26.
    * rewrite Q11. exact R18.
Qed.

(* ---------------- 0x840c0: check_object(rc, &res, &x), then 0x83870 .. check_cells ---------------- *)
Lemma br_obj : forall cx r ev POST fx2 ly2 S2 W2 regs2 mem2 md2,
@hqu_start_M03 fx rc SK rsegs B cx r ev -> @hqu_from_FIRST fx rc SK rsegs B MT cx r POST ->
br_inv cx r fx2 ly2 S2 W2 regs2 mem2 md2 ->
getr regs2 1 = w64 BR_OBJ_RET -> getr regs2 10 = w64 (e_rc (x_e rsegs cx)) ->
getr regs2 11 = w64 (e_F (x_e rsegs cx) + HQU_RES) -> getr regs2 12 = w64 (e_F (x_e rsegs cx) + HQU_XO) ->
SRr rsegs W2 (@cfg_at fx2 rsegs BR_CK_OBJECT regs2 mem2 md2) POST.
Proof.
intros cx r ev POST fx2 ly2 S2 W2 regs2 mem2 md2 HS HF Hinv Hra H10 H11 H12.
destruct (br_start cx r ev HS) as (HP & Hwf & Hown & HF0 & H32 & H4k & Hc & HR & HR47 & Hcap & Hnull & Hout & Hrc
  & Hrcb & Hs1 & Hs2 & Hc47).
pose proof Hinv as (Hb & Hat & Hx & Hcor).
pose proof Hb as (Hcore & Hfxk & Hfsh & _ & _ & _ & _ & Hres & _).
pose proof Hcore as (HJ & _).
pose proof (br_frame_at cx r ev ly2 S2 W2 mem2 md2 HS HJ) as HFa.
pose proof (hbe_hc_core B MT cx _ _ ly2 S2 W2 regs2 mem2 md2 HP Hcore) as HC.
eapply (@hc_call_ck fx2 rc SK rsegs B MT BR_CK_OBJECT BR_OBJ_RET POST); [exact HC | exact Hra | unfold BR_OBJ_RET; lia | reflexivity | |].
- intros HPre.
  assert (Hx' : garr8 rsegs (mrestrict (w_H W2) mem2) (e_F (x_e rsegs cx) + 0x2c0)
    (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null (x_e rsegs cx) =? 0)) (e_cap (x_e rsegs cx)) r))))
    by (rewrite (br_null_flag _ Hnull); exact Hx).
  assert (Hfsh' : hd_fsh rsegs (w_H W2) mem2 (e_F (x_e rsegs cx)) headamp_B_shX) by (rewrite br_shX; exact Hfsh).
  destruct (headamp_B_site_object rsegs B _ _ _ _ _ _ _ _ _ _ regs2 ly2 S2 W2 mem2 md2 (x_e rsegs cx) (x_pos rsegs cx)
    r (hqu_ans rsegs cx r) HPre Hown HFa Hfsh' Hwf Hcor Hcap eq_refl Hres Hx')
    as (Hrb & XV & XA & XO & XP & X4 & Hm1).
  rewrite Hrc in H10.
  eapply (CK_OBJ fx2); [exact HPre | exact H10 | exact H11 | exact H12 | exact Hrb | exact Hrb | tauto | exact XV
    | exact XA | exact XO | exact XP | exact X4 | exact Hm1].
- br_cont.
  pose proof (br_inv_call cx r ev fx2 ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 HS Hinv HC3 Hpres Hfr Hperm Hio Hmo
    Hkeep) as Hinv3.
  pose proof Hinv3 as ((Hcore3 & _) & Hat3 & _).
  pose proof Hcore3 as (HJ3 & _).
  eapply SRr_bind; [apply (@br_blk_obj_ret fx2 rc SK B MT MTL _ _ _ _ _ _ _ _ _ ly3 S3 W3 mem3 md3 (x_k rsegs cx) regs3 HJ3)|].
  intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & Hkr4 & Hfr4 & Hperm4 & Hio4 & Hmo4 & Hkeep4 & (Q1 & Q10 & Q11 & Q12)).
  pose proof (hbe_at_get _ _ _ _ _ 22 (e_out (x_e rsegs cx)) Hat3
    ltac:(unfold br_L, hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R22.
  pose proof (hbe_at_get _ _ _ _ _ 25 (e_rc (x_e rsegs cx)) Hat3
    ltac:(unfold br_L, hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R25.
  pose proof (hbe_at_get _ _ _ _ _ 18 (e_F (x_e rsegs cx) + HQU_XO) Hat3
    ltac:(unfold br_L, hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R18.
  apply (br_cells cx r ev POST fx2 ly4 S4 W4 regs4 mem4 md4 HS HF).
  + apply (br_inv_blk cx r ev fx2 ly3 S3 W3 regs3 mem3 md3 ly4 S4 W4 regs4 mem4 md4 [1; 10; 11; 12]%bv HS Hinv3 HJ4 Hkr4
      eq_refl Hfr4 Hperm4 Hio4 Hmo4).
    intros a Ha. apply Hkeep4; [exact Ha | intros []].
  + exact Q1.
  + rewrite Q10. exact R22.
  + rewrite Q11. exact R25.
  + rewrite Q12. exact R18.
Qed.

(* ---------------- RCM 0x8385c: x->rc := a3, then check_object ---------------- *)
Lemma br_from_RCM : forall cx r ev POST,
@hqu_start_M03 fx rc SK rsegs B cx r ev -> @hqu_from_FIRST fx rc SK rsegs B MT cx r POST ->
@hqu_from_RCM fx rc SK rsegs B MT cx r POST.
Proof.
intros cx r ev POST HS HF. unfold hqu_from_RCM. intros fx2 ly2 S2 W2 regs2 mem2 md2 HC.
destruct (br_start cx r ev HS) as (HP & Hwf & Hown & HF0 & H32 & H4k & Hc & HR & HR47 & Hcap & Hnull & Hout & Hrc
  & Hrcb & Hs1 & Hs2 & Hc47).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
destruct (hbe_seg B cx _ HP) as (_ & _ & _ & _ & _ & _ & HFapp & _).
destruct HC as (Hb & Hat & Hcor & Hxat).
pose proof Hb as (Hcore & Hfxk & Hfsh & _).
pose proof Hcore as (HJ & _).
destruct (br_exp_len cx r ev HS Hcor) as (Hlc & Hxl & Eae).
pose proof (br_x_geo cx r ev HS) as (Hx0 & Hx1 & Hx2 & Hx4).
pose proof (br_frame_at cx r ev ly2 S2 W2 mem2 md2 HS HJ) as HFa.
unfold hsu_at_cx, hsu_at in Hat.
pose proof (hbe_at_get _ _ _ _ _ 18 (e_F (x_e rsegs cx) + HQU_XO) Hat
  ltac:(unfold hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R18.
pose proof (hbe_at_get _ _ _ _ _ 13 (ans_rc (hqu_exp rsegs cx r)) Hat
  ltac:(unfold hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R13.
pose proof (hbe_at_get _ _ _ _ _ 25 (e_rc (x_e rsegs cx)) Hat
  ltac:(unfold hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R25.
pose proof (hbe_at_get _ _ _ _ _ 26 (e_F (x_e rsegs cx) + HQU_RES) Hat
  ltac:(unfold hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R26.
eapply SRr_bind.
{ apply (@br_blk_rcm fx2 rc SK B MT MTL _ _ _ _ _ _ _ _ _ ly2 S2 W2 mem2 md2 (x_k rsegs cx) regs2 (x_pos rsegs cx)
    (e_F (x_e rsegs cx) + HQU_XO) HJ Hown); [rewrite <- HFa; unfold HQU_XO in *; lia | rewrite <- HFa; unfold HQU_XO in *; lia
    | exact Hx0 | exact R18]. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr & Hfr & Hperm & Hio & Hmo & Hkeep & (Q1 & Q10 & Q11 & Q12 & QV)).
set (xa := e_F (x_e rsegs cx) + HQU_XO) in *.
assert (Hnx : forall a, 0 <= a < 2 ^ 64 -> ~ (xa <= a < xa + 4) -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a)
  by exact Hkeep.
assert (Hreg : forall q, 0 < q < 32 -> forallb (fun c => negb (bv_unsigned c =? q)) [1; 10; 11; 12]%bv = true ->
  getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q))
  by (intros q Hq Hcb; exact (br_reg_kept regs2 regs3 _ q Hkr Hq Hcb)).
assert (Hcore3 : hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
{ apply (hbe_core_blk B MT MTL cx (hqu_E3 rsegs B cx) (fun a => xa <= a < xa + 4) [1; 10; 11; 12]%bv
    ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hcore HJ3 Hkr);
  [ intros q Hq; destruct Hq as [->|[->| ->]]; (apply br_not_in_bv; [lia | reflexivity])
  | exact Hfr | exact Hperm | exact Hio | exact Hmo | exact Hkeep
  | intros a Ha; apply (hbe_wz_E3 B cx a); left; subst xa; lia ]. }
apply (br_obj cx r ev POST fx2 ly3 S3 W3 regs3 mem3 md3 HS HF).
- split.
  { apply (hbe_base3_kept B MT errno_low cx r ev fx2 fx2 hqu_shX hqu_shX ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
      HS Hb Hcore3); [| |exact Hfxk].
    - intros a Ha Hw. apply Hnx; [exact Ha|]. intros Hs. apply Hw. right. left. subst xa. lia.
    - unfold hsu_fsh_at in *. apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh).
      intros i Hi. rewrite hqu_shX_len in Hi. change (Z.of_nat 116) with 116 in Hi. apply Hnx; [lia|].
      unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp. subst xa. unfold HQU_XO in *. lia. }
  split.
  { unfold hsu_at_cx, hsu_at.
    assert (Hat3 : Forall (fun f => hd_at rsegs (w_H W3) mem3 regs3 (x_e rsegs cx) (fst f) (snd f))
      (hqu_L_seg rsegs cx ++ [(LReg 13, ans_rc (hqu_exp rsegs cx r)); (LReg 18, xa); (LReg 21, e_F (x_e rsegs cx));
        (LCell XR 0x18, e_F (x_e rsegs cx)); (LCell XR 0x48, e_F (x_e rsegs cx));
        (LCell XR 0x140, hd_xv (x_e rsegs cx) XProps); (LCell XR 0x148, e_pp (x_e rsegs cx));
        (LCell XR 0x150, 3 * e_cap (x_e rsegs cx) + 3); (LCell XR 0x158, e_pod (x_e rsegs cx))])).
    { apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ Hat).
      unfold T_SEG_STK, ASTACK in *.
      intros f Hf. unfold hqu_L_seg, hqu_L_frame in Hf. cbn [app In] in Hf.
      repeat (destruct Hf as [<-|Hf];
        [ cbn [hm_keeps fst hd_xv];
          first [ apply Hreg; [lia | reflexivity]
                | intros i Hi; apply Hnx; subst xa; unfold HQU_XO in *; lia ] |]).
      destruct Hf. }
    apply (hbe_at_sub _ _ _ _ _ _ Hat3).
    intros y Hy. unfold br_L, hqu_L_seg, hqu_L_frame in *. cbn [In app] in Hy |- *. subst xa.
    repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy. }
  split.
  { destruct Hxat as (Hxb & _).
    pose proof (hbe_exp_n cx r) as (Hn & _).
    apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
    rewrite <- (br_x_store (hqu_exp rsegs cx r) Hlc Hn).
    apply (hm_bytes_store rsegs (w_H W2) mem2 (w_H W3) mem3 xa _ 0 4
      (bv_unsigned (Z_to_bv 64 (ans_rc (hqu_exp rsegs cx r))) mod 2 ^ 32)
      (proj2 (hm_bytes_zbytes rsegs _ _ _ _) Hxb)).
    - rewrite Z.add_0_r.
      assert (E13 : bv_unsigned (getr regs2 13) = bv_unsigned (Z_to_bv 64 (ans_rc (hqu_exp rsegs cx r))))
        by (f_equal; exact R13).
      rewrite E13 in QV. exact QV.
    - rewrite hqu_x_open_len by exact Hlc. lia.
    - intros y Hy Hn4. rewrite hqu_x_open_len in Hy by exact Hlc. apply Hnx; [subst xa; lia | cbn in Hn4; lia]. }
  exact Hcor.
- exact Q1.
- rewrite Q10. exact R25.
- rewrite Q11. exact R26.
- rewrite Q12. exact R18.
Qed.

(* ---------------- RC 0x83850: s2 := x, a3 := x->n, s5 := F, then RCM ---------------- *)
Lemma br_from_RC : forall cx r ev POST,
@hqu_start_M03 fx rc SK rsegs B cx r ev -> @hqu_from_FIRST fx rc SK rsegs B MT cx r POST ->
@hqu_from_RC fx rc SK rsegs B MT cx r POST.
Proof.
intros cx r ev POST HS HF. unfold hqu_from_RC. intros fx2 ly2 S2 W2 regs2 mem2 md2 HC.
destruct (br_start cx r ev HS) as (HP & Hwf & Hown & HF0 & H32 & H4k & Hc & HR & HR47 & Hcap & Hnull & Hout & Hrc
  & Hrcb & Hs1 & Hs2 & Hc47).
pose proof (@ASAN_CEIL_range rc) as [[Hc1 Hc2] _]. unfold ASAN_CEIL in Hc1, Hc2.
destruct HC as (Hb & Hat & Hcor & Hrcn & Hxat).
pose proof Hb as (Hcore & Hfxk & Hfsh & _).
pose proof Hcore as (HJ & _).
destruct (br_exp_len cx r ev HS Hcor) as (Hlc & Hxl & Eae).
pose proof (br_x_geo cx r ev HS) as (Hx0 & Hx1 & Hx2 & Hx4).
unfold hsu_at_cx, hsu_at in Hat.
pose proof (hbe_at_get _ _ _ _ _ 9 (e_R (x_e rsegs cx)) Hat
  ltac:(unfold hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as R9.
pose proof (hbe_at_cell _ _ _ _ _ XR 0x48 (e_F (x_e rsegs cx)) Hat
  ltac:(unfold hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as C48.
pose proof (hbe_at_cell _ _ _ _ _ XR 0x138 (e_F (x_e rsegs cx) + HQU_XO) Hat
  ltac:(unfold hqu_L_seg, hqu_L_frame; cbn [In app]; repeat (first [left; reflexivity | right]))) as C138.
cbn [hd_xv] in C48, C138.
rewrite Z.mod_small in C48 by (unfold T_SEG_STK, ASTACK in *; lia).
rewrite Z.mod_small in C138 by (unfold HQU_XO, T_SEG_STK, ASTACK in *; lia).
destruct Hxat as (Hxb & Hxl10 & Hxcap & Hxkeys & Hxk & Hxrf).
pose proof (br_x_n (w_H W2) mem2 (e_F (x_e rsegs cx) + HQU_XO) _ _ _ Hlc Hxb) as Vn.
unfold X_CELLS in Hlc.
eapply SRr_bind.
{ apply (@br_blk_rc fx2 rc SK B MT MTL _ _ _ _ _ _ _ _ _ ly2 S2 W2 mem2 md2 (x_k rsegs cx) regs2 (e_R (x_e rsegs cx))
    (e_F (x_e rsegs cx)) (e_F (x_e rsegs cx) + HQU_XO) (Z.of_nat (length (ans_cells (hqu_exp rsegs cx r))))
    HJ R9); unfold T_SEG_STK, ASTACK, HQU_XO in *; try lia; [exact C48 | exact C138 | exact Vn]. }
intros W3 c3 _ (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & Hkr & Hfr & Hperm & Hio & Hmo & Hkeep & (Q18 & Q13 & Q21)).
assert (Hreg : forall q, 0 < q < 32 -> forallb (fun c => negb (bv_unsigned c =? q)) [13; 18; 21]%bv = true ->
  getr regs3 (Z_to_bv 5 q) = getr regs2 (Z_to_bv 5 q))
  by (intros q Hq Hcb; exact (br_reg_kept regs2 regs3 _ q Hkr Hq Hcb)).
assert (Hkeep' : forall a, 0 <= a < 2 ^ 64 -> aview rsegs (w_H W3) mem3 a = aview rsegs (w_H W2) mem2 a)
  by (intros a Ha; apply Hkeep; [exact Ha | intros []]).
assert (Hcore3 : hsu_core rsegs B MT cx (hqu_E3 rsegs B cx) ly3 S3 W3 regs3 mem3 md3).
{ apply (hbe_core_blk B MT MTL cx (hqu_E3 rsegs B cx) (fun _ => False) [13; 18; 21]%bv
    ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3 Hcore HJ3 Hkr);
  [ intros q Hq; destruct Hq as [->|[->| ->]]; (apply br_not_in_bv; [lia | reflexivity])
  | exact Hfr | exact Hperm | exact Hio | exact Hmo | exact Hkeep | intros a [] ]. }
apply (br_from_RCM cx r ev POST HS HF fx2 ly3 S3 W3 regs3 mem3 md3).
split.
{ apply (hbe_base3_kept B MT errno_low cx r ev fx2 fx2 hqu_shX hqu_shX ly2 S2 W2 regs2 mem2 md2 ly3 S3 W3 regs3 mem3 md3
    HS Hb Hcore3 (fun a Ha _ => Hkeep' a Ha)); [|exact Hfxk].
  unfold hsu_fsh_at in *. apply (hm_fsh_kept rsegs _ _ _ _ _ _ Hfsh).
  intros i Hi. rewrite hqu_shX_len in Hi. change (Z.of_nat 116) with 116 in Hi. apply Hkeep'. lia. }
split.
{ unfold hsu_at_cx, hsu_at.
  assert (HatS : Forall (fun f => hd_at rsegs (w_H W2) mem2 regs2 (x_e rsegs cx) (fst f) (snd f))
    (hqu_L_seg rsegs cx ++
     [(LCell XR 0x18, e_F (x_e rsegs cx)); (LCell XR 0x48, e_F (x_e rsegs cx));
      (LCell XR 0x140, hd_xv (x_e rsegs cx) XProps); (LCell XR 0x148, e_pp (x_e rsegs cx));
      (LCell XR 0x150, 3 * e_cap (x_e rsegs cx) + 3); (LCell XR 0x158, e_pod (x_e rsegs cx))])).
  { apply (hbe_at_sub _ _ _ _ _ _ Hat). intros y Hy. unfold hqu_L_seg, hqu_L_frame in *. cbn [In app] in Hy |- *.
    repeat (destruct Hy as [<-|Hy]; [repeat (first [left; reflexivity | right]) |]); destruct Hy. }
  assert (Hat3 : Forall (fun f => hd_at rsegs (w_H W3) mem3 regs3 (x_e rsegs cx) (fst f) (snd f))
    (hqu_L_seg rsegs cx ++
     [(LCell XR 0x18, e_F (x_e rsegs cx)); (LCell XR 0x48, e_F (x_e rsegs cx));
      (LCell XR 0x140, hd_xv (x_e rsegs cx) XProps); (LCell XR 0x148, e_pp (x_e rsegs cx));
      (LCell XR 0x150, 3 * e_cap (x_e rsegs cx) + 3); (LCell XR 0x158, e_pod (x_e rsegs cx))])).
  { apply (hm_atl_kept rsegs _ _ _ _ _ _ _ _ HatS).
    intros f Hf. unfold hqu_L_seg, hqu_L_frame in Hf. cbn [app In] in Hf.
    repeat (destruct Hf as [<-|Hf];
      [ cbn [hm_keeps fst hd_xv];
        first [ apply Hreg; [lia | reflexivity]
              | intros i Hi; apply Hkeep'; unfold T_SEG_STK, ASTACK in *; lia ] |]).
    destruct Hf. }
  apply Forall_app. split.
  - apply (proj1 (Forall_app _ _ _) Hat3).
  - apply Forall_cons; [cbn [hd_at fst snd]; rewrite Hrcn; exact Q13|].
    apply Forall_cons; [cbn [hd_at fst snd]; exact Q18|].
    apply Forall_cons; [cbn [hd_at fst snd]; exact Q21|].
    exact (proj2 (proj1 (Forall_app _ _ _) Hat3)). }
split; [exact Hcor|].
split; [|exact (conj Hxl10 (conj Hxcap (conj Hxkeys (conj Hxk Hxrf))))].
apply (proj1 (hm_bytes_zbytes rsegs _ _ _ _)).
apply (hm_bytes_kept rsegs _ _ _ _ _ _ (proj2 (hm_bytes_zbytes rsegs _ _ _ _) Hxb)).
intros y Hy. apply Hkeep'. rewrite hqu_x_open_len in Hy by (unfold X_CELLS; lia). unfold HQU_XO in *. lia.
Qed.

(* ======================================= the piece ======================================= *)
Theorem hbe_piece_M3e_rc : @hqu_piece_M3e_rc_stmt fx rc SK rsegs B MT.
Proof.
unfold hqu_piece_M3e_rc_stmt. intros cx POST r ev HS HF. split.
- exact (br_from_RC cx r ev POST HS HF).
- exact (br_from_RCM cx r ev POST HS HF).
Qed.
Print Assumptions hbe_piece_M3e_rc.
End d.
End c.
Print Assumptions hbe_piece_M3e_rc.
