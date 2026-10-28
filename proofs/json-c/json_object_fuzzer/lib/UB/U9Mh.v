(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup Q5Rg QCcH Q0Ek Qsw7 QJjn UPIU QQLG QnCn Q0Hd Lib.CodeAt Lib.StepGen Lib.StepGenX Lib.StepGenX2 Lib.GwCallee Lib.GwApply Lib.GwApply2 Lib.GwApplyJ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From Stdlib Require Permutation.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH QHnV QfLs QRUw QgoP Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QXup.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek.
Import UPIU.Mq6.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_3. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_idioms_in H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_idioms_in_4 H. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap e ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_1 e. Local Ltac OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.zs_wrap_in e H ::= OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.mkr__zs_wrap_in_2 e H.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.

Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.

Section G.
Variables (segs : list Segment).
Variables (e_blk_16e24 e_blk_16f30 e_blk_17684 e_blk_17710 e_blk_17718 : Z).

Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.

Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).

Let S4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let S4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
Variables (GGOT4 GHASH4 GVDSO4 JG_CGT_P gRDATA_LO : Z).
Hypothesis CS_GHASH4 : forall a, (GHASH4 <= a < GHASH4 + 12)%Z -> gCS a.
Hypothesis CS_GGOT4 : forall a, (GGOT4 <= a < GGOT4 + 8)%Z -> gCS a.
Hypothesis CS_GVDSO4 : forall a, (GVDSO4 <= a < GVDSO4 + 8)%Z -> gCS a.
Hypothesis LAY_RDATA_GGOT4 : gw_le gRDATA_LO GGOT4.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4x12_GVDSO4 : gw_le (GHASH4 + 12) GVDSO4.
Hypothesis LAY_IMG_GGOT4 : gw_le gIMG_LO GGOT4.
Hypothesis LAY_GVDSO4_IMG : gw_le (GVDSO4 + 8) gIMG_HI.
#[using="e_blk_16e24 e_blk_16f30 e_blk_17684 e_blk_17710 e_blk_17718 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free GGOT4 GHASH4 GVDSO4 JG_CGT_P gRDATA_LO CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG S4F"] Lemma gw_all : True. Proof. exact I. Qed.
Definition jc_glob_P := ltac:(gw_ctx2 (@UPIU.Mq6.jc_glob_P)).

Section RC__1.

Fixpoint okmax (l : list (option jshape)) : Z :=
match l with [] => 0 | None :: l' => okmax l' | Some s :: l' => Z.max (sdepth s) (okmax l') end.
Definition odep (o : option jshape) : Z := match o with None => 0 | Some s => sdepth s end.
#[using="Type"] Lemma kmax_nonneg : forall l, 0 <= (fix kmax (l0 : list (option jshape)) : Z := match l0 with [] => 0 | None :: l' => kmax l' | Some s' :: l' => Z.max (sdepth s') (kmax l') end) l.
Proof. clear - segs. induction l as [|[x|] l IHl]; cbn; lia. Qed.
#[using="Type"] Lemma sdepth_nonneg : forall s, 0 <= sdepth s.
Proof. clear - segs. intros [| | | |kids|kids]; cbn -[Z.add Z.max]; try lia; pose proof (kmax_nonneg kids); lia. Qed.

#[using="Type"] Lemma odep_nonneg : forall o, 0 <= odep o.
Proof. clear - segs. intros [s|]; cbn; [apply sdepth_nonneg | lia]. Qed.

Section JoStmts.
Variable L : heap_layout.
Variable HIx : heap_iface L.
Variable fn : fnaddrs.
Variable G : (word -> option byte) -> Prop.
Notation segs_ := (hl_segs L).

Definition jo_pre (A : AS L HIx) (LBall : list blk) (m : word -> option byte) (md : Model)
(sp tp ra : word) (lo stkb : Z) (errv : word) : Prop :=
HEAP L HIx A LBall m md /\
stk segs_ m lo (bv_unsigned sp) /\ alloc_ceiling <= lo /\ lo <= bv_unsigned sp - stkb /\
bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= hi_top L HIx /\
rw_cells segs_ m (hl_tp L - 164) [C4 errv] /\
tp = Z_to_bv 64 (hl_tp L) /\ bv_unsigned ra mod 2 = 0.

Definition jo_post_frame (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : Model) : Prop :=
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs_ m' lo (bv_unsigned sp) /\
heap_pres L LB (bv_unsigned sp) m m' /\
(exists errv', rw_cells segs_ m' (hl_tp L - 164) [C4 errv']).

Definition jo_post_framex (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(r : Z) (m' : word -> option byte) (ms' : machine_state) (md' : Model) : Prop :=
ret_statew L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs_ m' lo (bv_unsigned sp) /\
heap_presx L (hl_volatile L) LB (bv_unsigned sp) m m' /\
(exists errv', rw_cells segs_ m' (hl_tp L - 164) [C4 errv']).

Definition jo_new_container_stmt (entry stkb : Z) (s : jshape) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB : list blk) (lo : Z) (errv : word),
jo_pre A LB m md sp tp ra lo stkb errv -> G m ->
(forall ms' md' m' r, jo_post_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
((r = 0 /\ exists A', HEAP L HIx A' LB m' md') \/
(r <> 0 /\ exists A' BS, jval segs_ fn s m' BS r 1 /\ HEAP L HIx A' (BS ++ LB) m' md')) ->
realizes segs_ (mkCfg ms' md') T) ->
realizes segs_ (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs_)) md) T.

Definition jo_array_add_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS VBS : list blk) (lo p v : Z) (kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_pre A (ABS ++ VBS ++ LB) m md sp tp ra lo stkb errv ->
jval segs_ fn (Sarr kids) m ABS p 1 -> jopt segs_ fn vs m VBS v ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 v ->
(forall ms' md' m' r, jo_post_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
((r = 0 /\ exists A' ABS', jval segs_ fn (Sarr (kids ++ [vs])) m' ABS' p 1 /\ HEAP L HIx A' (ABS' ++ LB) m' md') \/
(r = 2^64 - 1 /\ exists A', jval segs_ fn (Sarr kids) m' ABS p 1 /\ jopt segs_ fn vs m' VBS v /\ HEAP L HIx A' (ABS ++ VBS ++ LB) m' md')) ->
realizes segs_ (mkCfg ms' md') T) ->
realizes segs_ (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs_)) md) T.

Definition jo_array_shrink_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB ABS : list blk) (lo p : Z) (kids : list (option jshape)) (errv : word),
jo_pre A (ABS ++ LB) m md sp tp ra lo stkb errv ->
jval segs_ fn (Sarr kids) m ABS p 1 -> a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 0 ->
(forall ms' md' m' r, jo_post_frame ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' ->
(exists A' ABS', jval segs_ fn (Sarr kids) m' ABS' p 1 /\ HEAP L HIx A' (ABS' ++ LB) m' md') ->
realizes segs_ (mkCfg ms' md') T) ->
realizes segs_ (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs_)) md) T.

Definition jo_object_add_stmt (entry stkb : Z) : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS L HIx) (LB OBS VBS : list blk) (lo p v k kn : Z) (ks : list byte) (kids : list (option jshape)) (vs : option jshape) (errv : word),
jo_pre A (OBS ++ VBS ++ LB) m md sp tp ra lo stkb errv -> G m ->
jval segs_ fn (Sobj kids) m OBS p 1 -> jopt segs_ fn vs m VBS v ->
In (k, kn) LB -> cstr segs_ m k kn ks -> kn <= 2^31 ->
frm0 fc ->
a0 = Z_to_bv 64 p -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 v ->
(forall ms' md' m' r, jo_post_framex ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo r m' ms' md' -> G m' ->
((r = 0 /\ exists A' OBS' kids', jval segs_ fn (Sobj kids') m' OBS' p 1 /\ HEAP L HIx A' (OBS' ++ LB) m' md'
/\ Z.of_nat (length kids') <= Z.of_nat (length kids) + 1
/\ okmax kids' <= Z.max (okmax kids) (odep vs)) \/
(r = 2^64 - 1 /\ exists A' REM, jval segs_ fn (Sobj kids) m' OBS p 1 /\ jopt segs_ fn vs m' VBS v /\ HEAP L HIx A' (OBS ++ VBS ++ REM ++ LB) m' md')) ->
realizes segs_ (mkCfg ms' md') T) ->
realizes segs_ (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 entry) fc None m (seg_rom segs_)) md) T.

End JoStmts.

Definition jo_new_object_P (HIx : heap_iface S4L) := jo_new_container_stmt S4L HIx S4F jc_glob_P (e_blk_16e24 + 0x0) (48 + 48 + 8256) (Sobj []).
Definition jo_new_array_P (HIx : heap_iface S4L) := jo_new_container_stmt S4L HIx S4F (fun _ => True) (e_blk_17684 + 0x0) (32 + 32 + 8256) (Sarr []).
Definition jo_array_add_P (HIx : heap_iface S4L) := jo_array_add_stmt S4L HIx S4F (e_blk_17710 + 0x0) (64 + 8256).
Definition jo_array_shrink_P (HIx : heap_iface S4L) := jo_array_shrink_stmt S4L HIx S4F (e_blk_17718 + 0x0) (64 + 8256).
Definition jo_object_add_P (HIx : heap_iface S4L) := jo_object_add_stmt S4L HIx S4F jc_glob_P (e_blk_16f30 + 0x0) (96 + 64 + 64 + 8256 + 2048).

End RC__1.

End G.
End Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q8tj QVbl QSL3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QPIU QRGY QXOI QnCn Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QCcH Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QgoP.
Import QVbl.Mq5.
Import QSL3.
Import QPIU.Mqb.
Import QRGY.Mq0.
Import QXOI.
Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm; gwj_align_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm; gwj_align_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition lhlookup_code : list Z :=
[0xfb010113; 0x04113423; 0x04813023; 0x02913c23; 0x03213823; 0x03313423; 0x03413023; 0x01513c23; 0x01613823; 0x01713423; 0x10050863; 0x00050413; 0x00757513; 0x10051263; 0x00058493; 0x00042583; 0x0e058c63; 0x0cb05263; 0x00000993; 0x02b67933; 0x02800a13; 0xffe00a93; 0xfff00b13; 0x0280006f; 0x00042583; 0x0019899b; 0x00190513; 0x0019091b; 0x0125c633; 0x00163613; 0xfff60613; 0x00a67933; 0x08b9d463; 0x01843603; 0x03490bb3; 0x00cb8533; 0x00c036b3; 0x00153713; 0x0ae68063; 0x08c56e63; 0x034916b3; 0x43fbd713; 0x00e6c6b3; 0x00d036b3; 0x08069463; 0x08060263; 0x00757613; 0x06061e63; 0x00053503; 0xfb5500e3; 0x05650063; 0x03043603; 0x00048593; 0x000600e7; 0xf80504e3; 0x01843503; 0x00ab8bb3; 0x04abea63; 0x00a035b3; 0x001bb613; 0x00c5c5b3; 0x04058263; 0x02800593; 0x02b905b3; 0x00b50533; 0x0080006f; 0x00000513; 0x04813083; 0x04013403; 0x03813483; 0x03013903; 0x02813983; 0x02013a03; 0x01813a83; 0x01013b03; 0x00813b83; 0x05010113; 0x00008067; 0xc0001073]%Z.

Lemma mul40_chk : forall n, 0 <= n -> n * 40 < 2^63 ->
v_sltu (Z_to_bv 64 0)
(Z_to_bv 64 (Z.lxor (bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 n) * 40) 64)))
(bv_unsigned (Z_to_bv 64 (Z.shiftr (bv_signed (Z_to_bv 64 (n * 40))) 63))))) = Z_to_bv 64 0.
Proof.
intros n H0 H1. rewrite !signed_lit by lia. rewrite !Z.shiftr_div_pow2 by lia. rewrite !Z.div_small by lia.
rewrite (unsigned_lit 0) by lia. change (Z.lxor 0 0) with 0. apply v_sltu_0'. rewrite !unsigned_lit; lia.
Qed.

Definition next_ix (size n : Z) : Z := if n + 1 =? size then 0 else n + 1.

Lemma land_ones64_l : forall x, 0 <= x < 2^64 -> Z.land 18446744073709551615 x = x.
Proof. intros x Hx. rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia. Qed.

Lemma remu_lit : forall a b, 0 <= a < 2^64 -> 0 < b < 2^64 ->
mul_div M_REMU (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a mod b).
Proof.
intros a b Ha Hb. unfold mul_div. rewrite (unsigned_lit b) by lia.
destruct (Z.eqb_spec b 0); [lia|]. apply bv_eq. rewrite bv_modu_unsigned, !unsigned_lit; try lia.
Qed.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section G.
Variables (segs : list Segment) (base : Z).
Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.
Hypothesis AL_gTP : gw_al gTP 4.
Hypothesis RNG_gTP : gw_br gTP 8.

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Variables (e_blk_18a54 e_strcmp : Z).
Hypothesis CODE : code_at segs base lhlookup_code.
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 316.

Definition lh_char_equal_post := ltac:(let t := constr:(ltac:(gw_callee_stmt (@QRGY.Mq0.gw_all) (@QRGY.Mq0.u_lh_char_equal_post) e_fn_lh_char_equal)) in let t := eval cbv beta delta [QRGY.Mq0.u_lh_char_equal_post] in t in exact t).

Hypothesis lh_char_equal_spec : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QRGY.Mq0.gw_all) (@QRGY.Mq0.u_lh_char_equal_spec) e_fn_lh_char_equal)) in let x := constr:(ltac:(gw_callee_stmt (@QRGY.Mq0.gw_all) (@QRGY.Mq0.u_lh_char_equal_post) e_fn_lh_char_equal)) in let T := gw_subst T x lh_char_equal_post in exact T).

Hypothesis ent_addr_mod8 : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@QXOI.gw_all) (@QXOI.ent_addr_mod8) (base + -112)%Z)) in let T := eval cbv beta delta [QXOI.u_lh_entry_free_entry QXOI.u_lh_table_free_entry] in T in let T := gw_fold_pcs T base (-112)%Z [0; 48; 80]%Z in let x := constr:(ltac:(gw_callee_stmt (@QRGY.Mq0.gw_all) (@QRGY.Mq0.u_lh_char_equal_post) e_fn_lh_char_equal)) in let T := gw_subst T x lh_char_equal_post in exact T).
Arguments ent_addr_mod8 _%_Z_scope _%_nat_scope.

Let S4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let S4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
Hypothesis AL_e_fn_lh_char_equal : gw_b4 e_fn_lh_char_equal.
Hypothesis RNG_e_fn_lh_char_equal : gw_br e_fn_lh_char_equal 4.
Hypothesis LAY_POS_e_fn_lh_char_equal : gw_le 1 e_fn_lh_char_equal.
Hypothesis LAY_HI_e_fn_lh_char_equal : gw_le (e_fn_lh_char_equal + 4) 1099511627776.
#[using="RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI AL_gTP RNG_gTP e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free e_blk_18a54 e_strcmp CODE BASE4 BASER lh_char_equal_spec ent_addr_mod8 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Ltac g_ra_even := lazymatch goal with |- (bv_unsigned (Z_to_bv 64 (?b + ?k)) mod 2 = 0)%Z =>
let X := fresh in let Y := fresh in pose proof BASE4 as X; pose proof BASER as Y; unfold gw_b4, gw_br in X, Y; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia end.
Ltac alloc_side ::=
try (progress fold S4L); try (progress fold S4F);
simpl hl_segs; simpl hl_stack; simpl hl_tp; simpl hl_malloc; simpl hl_free; simpl hl_calloc; simpl hl_realloc;
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _, _ => idtac
| |- _ \/ _ => idtac
| |- (bv_unsigned (Z_to_bv 64 (_ + _)) mod 2 = 0)%Z => first [ g_ra_even | lia ]
| |- _ =>
lazymatch goal with
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- (_ mod 16 = 0)%Z =>
first [ assumption
| match goal with H : (bv_unsigned ?sp mod 16 = 0)%Z |- ((bv_unsigned ?sp + ?k) mod 16 = 0)%Z =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia ]
end end.
Ltac gj_fold := try (progress fold S4L); repeat match goal with H : _ |- _ => progress fold S4L in H end; try (progress fold S4F); repeat match goal with H : _ |- _ => progress fold S4F in H end.
Ltac unfold_consts ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
Ltac clia ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Ltac unfold_consts_goal ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size.
Ltac gj_fn_cbn := try (progress cbn [S4F fn_lh_char_equal]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Definition lh_lookup_entry : Z := (base + 0x0).

Section LhLookup.
Variables (ra sp gp tp : word) (s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (t tbl size kp lo : Z) (es : list lent) (svs : list slotv) (ps : list byte).

Definition lookup_res (r : Z) : Prop :=
r = 0 \/ exists j e, nth_error es j = Some e /\ r = ent_addr tbl (le_ix e) /\ le_ks e = ps.

Definition lh_lookup_post (m : word -> option byte) : machine_state -> Prop :=
fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 (r : Z) m',
ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (ret_pc ra) fc None m' (seg_rom segs)
/\ munch [(bv_unsigned sp - 96, bv_unsigned sp)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ stk segs m' lo (bv_unsigned sp)
/\ lh_open segs S4F m' t tbl size es svs
/\ bytes_at segs m' kp (ps ++ [b0])
/\ lookup_res r.

Definition lk_frame (m : word -> option byte) (junk8 : list byte) : Prop :=
rw_cells segs m (bv_unsigned sp + -80) [CB 8 junk8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_char_equal CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma lh_lookup_next :
forall (n cnt : Z) (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 x22 t3 t4 t5 t6 : word) (m : word -> option byte),
0 <= cnt < size -> 0 <= n < size -> In size lf_sizes -> mem_inv segs m ->
evt segs (fun ms' =>
(cnt + 1 < size /\
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp)
(Z_to_bv 64 (n + 1)) (Z_to_bv 64 size) (Z_to_bv 64 (if n + 1 =? size then 0 else -1)) a3 a4 a5 a6 a7
(Z_to_bv 64 (next_ix size n)) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) x22 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x84)) fc None m (seg_rom segs))
\/ (cnt + 1 = size /\
ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp)
(Z_to_bv 64 (n + 1)) (Z_to_bv 64 size) (Z_to_bv 64 (if n + 1 =? size then 0 else -1)) a3 a4 a5 a6 a7
(Z_to_bv 64 (next_ix size n)) (Z_to_bv 64 (cnt + 1)) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) x22 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x108)) fc None m (seg_rom segs)))
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 n) (Z_to_bv 64 cnt) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) x22 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x64)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_char_equal CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until m. intros Hcnt Hn Hsz MI.
pose proof (lf_size_range size Hsz) as HSR. word_range sp SPR.
pose proof (munch_refl [] m) as MU. pose proof (wmono_refl segs m) as WM.
step. norm_w32. step. step. norm_w32. step. rewrite (unsigned_lit size), (unsigned_lit (n + 1)) by lia.
unfold next_ix. destruct (Z.eqb_spec (n + 1) size) as [EQ|NE].
- rewrite EQ, Z.lxor_nilpotent. step. rewrite (v_sltiu_1 (Z_to_bv 64 0) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. rewrite (unsigned_lit size) by lia. change (bv_unsigned (Z_to_bv 64 (1 + -1))) with 0. rewrite Z.land_0_l.
replace (1 + -1) with 0 by lia.
step.
destruct (Z.lt_ge_cases (cnt + 1) size).
+ if_falsex. apply evt_done. left. split; [lia | reflexivity].
+ if_truex. apply evt_done. right. split; [lia | reflexivity].
- pose proof (lxor_bound size (n + 1) 31 ltac:(lia) ltac:(lia) ltac:(lia)) as LB.
assert (LNZ : Z.lxor size (n + 1) <> 0) by (intros X; apply Z.lxor_eq in X; lia).
step. rewrite (v_sltiu_0 (Z_to_bv 64 (Z.lxor size (n + 1))) 1) by (rewrite ?unsigned_lit by lia; lia).
step. step. change (bv_unsigned (Z_to_bv 64 (0 + -1))) with 18446744073709551615.
rewrite (unsigned_lit (n + 1)) by lia. rewrite land_ones64_l by lia.
replace (0 + -1) with (-1) by lia.
step.
destruct (Z.lt_ge_cases (cnt + 1) size).
+ if_falsex. apply evt_done. left. split; [lia | reflexivity].
+ if_truex. apply evt_done. right. split; [lia | reflexivity].
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma lh_lookup_exit0 :
forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 t3 t4 t5 t6 : word) (m0 m : word -> option byte) (junk8 : list byte),
mem_inv segs m -> lh_open segs S4F m t tbl size es svs -> bytes_at segs m kp (ps ++ [b0]) ->
stk segs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 96 -> lk_frame m junk8 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m0 m -> wmono segs m0 m ->
evt segs (lh_lookup_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 a3 a4 a5 a6 a7
x18 x19 x20 x21 x22 x23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x108)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base S4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until junk8. intros MI OPEN PS ST LOS FR MU WM. unfold lk_frame in FR. word_range sp SPR.
step. do 10 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold lh_lookup_post. do 14 eexists. exists 0. eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact OPEN|]. split; [exact PS|].
left. reflexivity.
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma lh_lookup_exit1 :
forall (n : Z) (e : lent) (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 x20 x21 x22 t3 t4 t5 t6 : word) (m0 m : word -> option byte) (junk8 : list byte),
0 <= n < size -> In size lf_sizes -> In e es -> le_ix e = Z.to_nat n -> le_ks e = ps ->
mem_inv segs m -> lh_open segs S4F m t tbl size es svs -> lh_below lo t tbl size es -> 0 < tbl -> bytes_at segs m kp (ps ++ [b0]) ->
stk segs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 96 -> lk_frame m junk8 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m0 m -> wmono segs m0 m ->
evt segs (lh_lookup_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 n) x19 x20 x21 x22 (Z_to_bv 64 (n * 40)) s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xdc)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base S4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until junk8. intros Hn Hsz He Hix Hks MI OPEN BELOW Hblo PS ST LOS FR MU WM. unfold lk_frame in FR. word_range sp SPR.
pose proof OPEN as (HDR & _). unfold lh_hdr, lh_hdrf in HDR. pose proof BELOW as (Ht0 & Ht & Hb0 & Hb & _).
pose proof (lf_size_range size Hsz) as HSR. unfold_consts.
step. step. step. if_falsex.
step. step. step.
rewrite (v_sltu_1' (Z_to_bv 64 0) (Z_to_bv 64 tbl)) by (rewrite !unsigned_lit by lia; lia).
rewrite (v_sltiu_0 (Z_to_bv 64 (n * 40 + tbl)) 1) by (rewrite ?unsigned_lit by lia; lia).
rewrite !unsigned_lit by lia. change (Z.lxor 1 0) with 1.
step. if_false.
step. step. rewrite (unsigned_lit n) by lia. step.
do 11 step. release_frame FR ST (bv_unsigned sp). step.
apply evt_done. unfold lh_lookup_post. do 14 eexists. exists (tbl + n * 40). eexists.
split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact OPEN|]. split; [exact PS|].
right. destruct (In_nth_error _ _ He) as [j Hj]. exists j, e. split; [exact Hj|]. split; [unfold ent_addr; rewrite Hix; lia | exact Hks].
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER lh_char_equal_spec ent_addr_mod8 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma lh_lookup_loop :
forall (k : nat) (n cnt : Z) (x1 t0 t1 t2 a0 a2 a3 a4 a5 a6 a7 x23 t3 t4 t5 t6 : word) (m0 m : word -> option byte) (junk8 : list byte),
Z.of_nat k = size - cnt -> 0 <= cnt < size -> 0 <= n < size ->
mem_inv segs m ->
lh_open segs S4F m t tbl size es svs -> lh_below lo t tbl size es -> tbl mod 16 = 0 -> 0 < tbl ->
bytes_at segs m kp (ps ++ [b0]) -> ~ In b0 ps -> (kp + Z.of_nat (length ps) + 1 <= lo \/ bv_unsigned sp <= kp) ->
stk segs m lo (bv_unsigned sp + -80) -> lo <= bv_unsigned sp - 96 ->
lk_frame m junk8 ->
munch [(bv_unsigned sp - 96, bv_unsigned sp)] m0 m -> wmono segs m0 m ->
evt segs (lh_lookup_post m0)
(MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -80)) gp tp t0 t1 t2 (Z_to_bv 64 t) (Z_to_bv 64 kp) a0 (Z_to_bv 64 size) a2 a3 a4 a5 a6 a7
(Z_to_bv 64 n) (Z_to_bv 64 cnt) (Z_to_bv 64 40) (Z_to_bv 64 (-2)) (Z_to_bv 64 (-1)) x23 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x84)) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER lh_char_equal_spec ent_addr_mod8 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs base S4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
induction k as [|k IH]; intros until junk8; intros Hk Hcnt Hn MI OPEN BELOW Hbal Hblo PS NP SEPk ST LOS FR MU WM; [lia|].
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hc & Hlen). pose proof BELOW as (Ht0 & Ht & Hb0 & Hb & Hkb).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. pose proof FR as FR0. unfold lk_frame in FR. word_range sp SPR. unfold_consts.
pose proof (bytes_at_bound _ _ _ _ PS) as PSB. rewrite length_app in PSB. cbn [length] in PSB.
destruct (nth_error svs (Z.to_nat n)) as [sv|] eqn:Esv.
2:{ exfalso. apply nth_error_None in Esv. lia. }
pose proof (SL (Z.to_nat n) sv Esv) as C. unfold ent_addr, slot_cells in C. rewrite Z2Nat.id in C by lia.
pose proof (rw_cells_bound segs m _ _ C) as CB0. cbn [cells_size csize Nat.add] in CB0.

step. step. step. rewrite (unsigned_lit n) by lia.
step. step. ub_nzpair tbl (n * 40 + tbl). step. if_false.
step. if_falsex.
step. step. step. step. rewrite (mul40_chk n) by lia. step. if_false.
step. if_falsex.
step. rewrite (unsigned_lit (n * 40 + tbl)) by lia. rewrite (land7_of_mod8 (n * 40 + tbl)) by (replace (n * 40 + tbl) with (tbl + 40 * Z.of_nat (Z.to_nat n)) by lia; apply ent_addr_mod8; exact Hbal).
step. if_false.
replace (n * 40 + tbl) with (tbl + 40 * n) by lia.
remember (tbl + 40 * n) as B eqn:EB.
step. subst B.
destruct LINK as (LK1 & LK2 & LK3 & LK4).
destruct (in_dec Nat.eq_dec (Z.to_nat n) (map le_ix es)) as [LIVE|DEAD].
-
apply in_map_iff in LIVE. destruct LIVE as (e & Hix & He).
destruct (In_nth_error _ _ He) as [j Hj].
destruct (LK1 j e Hj) as (sv' & Esv' & Ek & Ekc & Ev & Enx & Epv). rewrite Hix, Esv in Esv'. injection Esv' as <-.
destruct (LK4 e He) as (Hk0 & HkF & Hkn31 & Hv). unfold LH_FREEDv in HkF.
destruct (lh_key_bytes segs m es e KEYS He) as (KB & KNZ & KL).
rewrite Ek.
step. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 (-2))) with 18446744073709551614. rewrite (unsigned_lit (le_k e)) by lia. if_false.
step. unfold bv_eqb. change (bv_unsigned (Z_to_bv 64 (-1))) with 18446744073709551615. rewrite (unsigned_lit (le_k e)) by lia. if_false.
step. step. step.

cbn [fn_lh_char_equal S4F]. gw_ret_pc_var_tac.
pose proof (Hkb e He) as Hke.
pose proof (munch_refl [(bv_unsigned sp + -96, bv_unsigned sp + -80)] m) as MUk. pose proof (wmono_refl segs m) as WMk.
eapply evt_cut.
{ eapply lh_char_equal_spec with (ls := le_ks e) (rs := ps) (lo := lo);
rewrite ?(unsigned_lit (le_k e)), ?(unsigned_lit kp), ?(unsigned_lit (bv_unsigned sp + -80)) by lia;
first [exact KB | exact PS | exact KNZ | exact NP | exact ST | exact MI | lia]. }
unfold lh_char_equal_post. cbv beta.
rewrite ?(unsigned_lit (le_k e)), ?(unsigned_lit kp), ?(unsigned_lit (bv_unsigned sp + -80)) by lia.
post_call segs m.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (OPEN' : lh_open segs S4F mx t tbl size es svs)
by (eapply (lh_open_frame segs S4F _ m mx); [exact OPEN | exact BELOW | exact MUk | exact WMk | apply Forall_cons; [cbn; lia | apply Forall_nil]]);
rename mx into m2 end.
match goal with H : stk segs m2 lo _ |- _ => rename H into ST2 end.
match goal with H : bytes_at segs m2 kp _ |- _ => rename H into PS2 end.
clear MUk WMk OPEN. try clear C. try clear PS. try clear ST.
destruct (Z.eqb_spec (strcmp_model (le_ks e) ps) 0) as [EQ0|NE0].
+
step. if_false.
eapply (lh_lookup_exit1 n e); first [exact OPEN' | exact BELOW | exact Hblo | exact PS2 | exact ST2 | exact MU | exact WM | exact He | exact Hix | exact Hsz | eassumption | idtac].
apply (proj1 (strcmp_model_zero _ _ KNZ NP)). exact EQ0.
+
step. if_true. step. norm_sx32.
match goal with H : mem_inv segs m2 |- _ => rename H into MI end.
eapply evt_cut; [eapply (lh_lookup_next n cnt); [lia | lia | exact Hsz | exact MI] |].
cbv beta. intros ms' [[Hlt' ->] | [Heq ->]].
* eapply (IH (next_ix size n) (cnt + 1));
first [exact OPEN' | exact BELOW | exact PS2 | exact NP | exact SEPk | exact ST2 | exact FR | exact MU | exact WM | exact MI | exact Hbal | exact Hblo | idtac];
unfold next_ix; try (destruct (Z.eqb_spec (n + 1) size)); lia.
* eapply lh_lookup_exit0; first [exact OPEN' | exact PS2 | exact ST2 | exact FR | exact MU | exact WM | exact MI | lia].
-
destruct (LK2 (Z.to_nat n) sv Esv DEAD) as [EK | FK]; rewrite EK || rewrite FK; unfold LH_EMPTYv, LH_FREEDv.
+ step. if_false. step. if_true.
eapply lh_lookup_exit0; first [exact OPEN | exact PS | exact ST | exact FR0 | exact MU | exact WM | exact MI | lia].
+ step. if_true.
eapply evt_cut; [eapply (lh_lookup_next n cnt); [lia | lia | exact Hsz | exact MI] |].
cbv beta. intros ms' [[Hlt' ->] | [Heq ->]].
* eapply (IH (next_ix size n) (cnt + 1));
first [exact OPEN | exact BELOW | exact PS | exact NP | exact SEPk | exact ST | exact FR0 | exact MU | exact WM | exact MI | exact Hbal | exact Hblo | idtac];
unfold next_ix; try (destruct (Z.eqb_spec (n + 1) size)); lia.
* eapply lh_lookup_exit0; first [exact OPEN | exact PS | exact ST | exact FR0 | exact MU | exact WM | exact MI | lia].
Qed.

#[using="gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER lh_char_equal_spec ent_addr_mod8 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal"] Lemma lh_lookup_spec :
forall (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : word -> option byte) (h : Z),
mem_inv segs m ->
lh_open segs S4F m t tbl size es svs -> lh_below lo t tbl size es -> t mod 16 = 0 -> tbl mod 16 = 0 -> 0 < t -> 0 < tbl ->
bytes_at segs m kp (ps ++ [b0]) -> ~ In b0 ps -> (kp + Z.of_nat (length ps) + 1 <= lo \/ bv_unsigned sp <= kp) ->
stk segs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 96 ->
a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 kp -> a2 = Z_to_bv 64 h -> 0 <= h < 2^64 ->
evt segs (lh_lookup_post m)
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_lookup_entry) fc None m (seg_rom segs)).
Proof. clear - gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI CODE BASE4 BASER lh_char_equal_spec ent_addr_mod8 AL_e_fn_lh_char_equal RNG_e_fn_lh_char_equal LAY_POS_e_fn_lh_char_equal LAY_HI_e_fn_lh_char_equal segs S4F ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc t tbl size kp lo es svs ps. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_POS_e_fn_lh_char_equal as gL2_; unfold gw_le in gL2_. pose proof LAY_HI_e_fn_lh_char_equal as gL3_; unfold gw_le in gL3_.
intros until h. intros MI OPEN BELOW Htal Hbal Htlo Hblo PS NP SEPk ST LOS A0 A1 A2 Hh.
pose proof OPEN as (HDR & SL & LINK & KEYS & Hsz & Hc & Hlen). pose proof BELOW as (Ht0 & Ht & Hb0 & Hb & Hkb).
pose proof (lf_thr_lt size Hsz) as Hlt. pose proof (lf_size_range size Hsz) as HSR.
unfold lh_hdr, lh_hdrf in HDR. word_range sp SPR. unfold_consts.
pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)] m) as MU. pose proof (wmono_refl segs m) as WM.
unfold lh_lookup_entry. subst a0 a1 a2.
carve_frame 80%nat ST.
do 10 step.
step. if_falsex. step. step. step. ubsan_align Htal.
step. step. norm_sx32. step. if_falsex. step. if_falsex.
step. step. rewrite remu_lit by lia. step. step. step. step.
pose proof (Z.mod_pos_bound h size ltac:(lia)) as HM.
eapply (lh_lookup_loop (Z.to_nat size) (h mod size) 0);
first [exact BELOW | exact PS | exact NP | exact SEPk | exact ST | exact MU | exact WM | exact MI | exact FR | exact Hbal | exact Hblo | lia | idtac].
eapply (lh_open_frame segs S4F _ m); [exact OPEN | exact BELOW | exact MU | exact WM | apply Forall_cons; [cbn; lia | apply Forall_nil]].
Qed.
End LhLookup.

End G.
End Mq3.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw QnCn Qrtz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq4.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup Q5Rg.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qsw7 QJjn QRUw Q8tj.
Import QSL3.
Import QnCn.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.

Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm; gwj_align_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm; gwj_align_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm; gwj_align_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition lhnew_code (w_7 w_8 w_12 w_21 w_26 w_27 w_45 : Z) : list Z :=
[0xfd010113; 0x02113423; 0x02813023; 0x00913c23; 0x01213823; 0x01313423; 0x00058493; w_7; w_8; 0x00050413; 0x00100513; 0x03800593; w_12; 0x08050463; 0x00757593; 0x08059e63; 0x00852023; 0x00052223; 0x02800593; 0x00050993; 0x00040513; w_21; 0x00050593; 0x00098513; 0x00b9bc23; 0x04058863; w_26; w_27; 0x02953023; 0x03253423; 0x02c53823; 0x04805063; 0x00000613; 0xfff5c693; 0x0075f713; 0x02800793; 0x02f407b3; 0xfff00813; 0x04c6e063; 0x02071e63; 0x00c588b3; 0x02860613; 0x0108b023; 0xfec796e3; 0x00c0006f; w_45; 0x00000513; 0x02813083; 0x02013403; 0x01813483; 0x01013903; 0x00813983; 0x03010113; 0x00008067; 0xc0001073]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_7 w_8 w_12 w_21 w_26 w_27 w_45 : Z).
Variables (hi_7 hi_26 : bv 20).
Variables (lo_8 lo_27 : bv 12).
Variables (joff_12 joff_21 joff_45 : bv 21).
Variables (GGOT4 GHASH4 GVDSO4 : Z).
Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.
Hypothesis AL_gTP : gw_al gTP 4.
Hypothesis RNG_gTP : gw_br gTP 8.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - gH2 gH3 LAY_gIMG_LO gTP gIMG_LO gIMG_HI. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.
#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI"] Lemma gLAYF0 : ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gTP gIMG_LO gIMG_HI. pose proof LAY_TPLO as X1; pose proof LAY_TPHI as X2; unfold gw_le in X1, X2. split; [split; [exact X1 | exact X2] | exact LAY_gIMG_LO]. Qed.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Variable vdso_ok4 : Z -> Prop.
Variables (JG_CGT_P gRDATA_LO : Z).
Hypothesis CODE : code_at segs base (lhnew_code w_7 w_8 w_12 w_21 w_26 w_27 w_45).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 220.
Hypothesis D_7 : decode_any (Z_to_bv 32 w_7) = Some (Auipc 11 hi_7, 4%Z).
Hypothesis E_7 : is_ecall (Z_to_bv 32 w_7) = false.
Hypothesis D_8 : decode_any (Z_to_bv 32 w_8) = Some (Load SZ8 true 18 11 lo_8, 4%Z).
Hypothesis E_8 : is_ecall (Z_to_bv 32 w_8) = false.
Hypothesis D_12 : decode_any (Z_to_bv 32 w_12) = Some (Jal 1 joff_12, 4%Z).
Hypothesis E_12 : is_ecall (Z_to_bv 32 w_12) = false.
Hypothesis D_21 : decode_any (Z_to_bv 32 w_21) = Some (Jal 1 joff_21, 4%Z).
Hypothesis E_21 : is_ecall (Z_to_bv 32 w_21) = false.
Hypothesis D_26 : decode_any (Z_to_bv 32 w_26) = Some (Auipc 12 hi_26, 4%Z).
Hypothesis E_26 : is_ecall (Z_to_bv 32 w_26) = false.
Hypothesis D_27 : decode_any (Z_to_bv 32 w_27) = Some (Load SZ8 true 12 12 lo_27, 4%Z).
Hypothesis E_27 : is_ecall (Z_to_bv 32 w_27) = false.
Hypothesis D_45 : decode_any (Z_to_bv 32 w_45) = Some (Jal 1 joff_45, 4%Z).
Hypothesis E_45 : is_ecall (Z_to_bv 32 w_45) = false.
Hypothesis ANCH_8 : gw_anch (Z.shiftl (bv_signed hi_7) 12 + (base + 28) + bv_signed lo_8)%Z GHASH4.
Hypothesis ANCH_27 : gw_anch (Z.shiftl (bv_signed hi_26) 12 + (base + 104) + bv_signed lo_27)%Z GGOT4.
Hypothesis LINK_12 : gw_anch (base + 48 + bv_signed joff_12)%Z e_calloc.
Hypothesis LINK_21 : gw_anch (base + 84 + bv_signed joff_21)%Z e_calloc.
Hypothesis LINK_45 : gw_anch (base + 180 + bv_signed joff_45)%Z e_free.
Hypothesis RNG_GGOT4 : gw_br GGOT4 8.
Hypothesis AL_GGOT4 : gw_al GGOT4 8.
Hypothesis RNG_GHASH4 : gw_br GHASH4 8.
Hypothesis AL_GHASH4 : gw_al GHASH4 8.
Hypothesis RNG_GVDSO4 : gw_br GVDSO4 8.
Hypothesis AL_GVDSO4 : gw_al GVDSO4 8.
Hypothesis LAY_GGOTU_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASHU_GVDSO4 : gw_le (GHASH4 + 8) GVDSO4.

Hypothesis CS_GHASH4 : forall a, (GHASH4 <= a < GHASH4 + 12)%Z -> gCS a.
Hypothesis CS_GGOT4 : forall a, (GGOT4 <= a < GGOT4 + 8)%Z -> gCS a.
Hypothesis CS_GVDSO4 : forall a, (GVDSO4 <= a < GVDSO4 + 8)%Z -> gCS a.

Hypothesis LAY_IMG_GGOT4 : gw_le gIMG_LO GGOT4.
Hypothesis LAY_GVDSO4_IMG : gw_le (GVDSO4 + 8) gIMG_HI.

Let S4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let S4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
Hypothesis LAY_RDATA_GGOT4 : gw_le gRDATA_LO GGOT4.
Hypothesis LAY_GGOT4_GHASH4 : gw_le (GGOT4 + 8) GHASH4.
Hypothesis LAY_GHASH4x12_GVDSO4 : gw_le (GHASH4 + 12) GVDSO4.
Hypothesis AL_e_fn_lh_entry_free : gw_b4 e_fn_lh_entry_free.
Hypothesis RNG_e_fn_lh_entry_free : gw_br e_fn_lh_entry_free 4.
Hypothesis LAY_POS_e_fn_lh_entry_free : gw_le 1 e_fn_lh_entry_free.
Hypothesis LAY_HI_e_fn_lh_entry_free : gw_le (e_fn_lh_entry_free + 4) 1099511627776.
#[using="w_7 w_8 w_12 w_21 w_26 w_27 w_45 hi_7 hi_26 lo_8 lo_27 joff_12 joff_21 joff_45 GGOT4 GHASH4 GVDSO4 RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI AL_gTP RNG_gTP e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free vdso_ok4 JG_CGT_P gRDATA_LO CODE BASE4 BASER D_7 E_7 D_8 E_8 D_12 E_12 D_21 E_21 D_26 E_26 D_27 E_27 D_45 E_45 ANCH_8 ANCH_27 LINK_12 LINK_21 LINK_45 RNG_GGOT4 AL_GGOT4 RNG_GHASH4 AL_GHASH4 RNG_GVDSO4 AL_GVDSO4 LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 AL_e_fn_lh_entry_free RNG_e_fn_lh_entry_free LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free S4F"] Lemma gw_all : True. Proof. exact I. Qed.

Ltac g_ra_even := lazymatch goal with |- (bv_unsigned (Z_to_bv 64 (?b + ?k)) mod 2 = 0)%Z =>
let X := fresh in let Y := fresh in pose proof BASE4 as X; pose proof BASER as Y; unfold gw_b4, gw_br in X, Y; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia end.
Ltac alloc_side ::=
try (progress fold S4L); try (progress fold S4F);
simpl hl_segs; simpl hl_stack; simpl hl_tp; simpl hl_malloc; simpl hl_free; simpl hl_calloc; simpl hl_realloc;
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _, _ => idtac
| |- _ \/ _ => idtac
| |- (bv_unsigned (Z_to_bv 64 (_ + _)) mod 2 = 0)%Z => first [ g_ra_even | lia ]
| |- _ =>
lazymatch goal with
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- (_ mod 16 = 0)%Z =>
first [ assumption
| match goal with H : (bv_unsigned ?sp mod 16 = 0)%Z |- ((bv_unsigned ?sp + ?k) mod 16 = 0)%Z =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia ]
end end.
Ltac gj_fold := try (progress fold S4L); repeat match goal with H : _ |- _ => progress fold S4L in H end; try (progress fold S4F); repeat match goal with H : _ |- _ => progress fold S4F in H end.
Ltac unfold_consts ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
Ltac clia ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Ltac unfold_consts_goal ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size.
Ltac gj_fn_cbn := try (progress cbn [S4F fn_lh_entry_free]).
Ltac if_truex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_condx] end.
Ltac if_falsex ::= gj_fn_cbn; lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_condx] end.
Ltac if_true ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Ltac if_false ::= gj_fn_cbn; first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Section RC__1.

Section LhNew.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition lh_kchar_table_new_entry : Z := (base + 0x0).

#[using="w_7 w_8 w_12 w_21 w_26 w_27 w_45 GGOT4 GHASH4 GVDSO4 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free gRDATA_LO CODE LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma lh_init_loop :
forall (k i n : nat) (x1 x2 gp tp t0 t1 t2 x8 x9 a0 a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (tbl : Z),
(k = n - 1 - i)%nat -> (i < n)%nat -> 0 <= tbl -> tbl + 40 * Z.of_nat n < 2^64 ->
mem_inv segs m ->
lh_slots segs m tbl (init_svs i n) ->
evt segs (fun ms' => exists m' a7',
ms' = MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 a0 (Z_to_bv 64 tbl) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (18446744073709551615 - tbl)) (Z_to_bv 64 0) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (-1)) a7' x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0xb0)) fc None m' (seg_rom segs)
/\ munch [(tbl, tbl + 40 * Z.of_nat n)] m m' /\ wmono segs m m' /\ mem_inv segs m'
/\ lh_slots segs m' tbl (init_svs n n))
(MS (mkR x1 x2 gp tp t0 t1 t2 x8 x9 a0 (Z_to_bv 64 tbl) (Z_to_bv 64 (40 * Z.of_nat i)) (Z_to_bv 64 (18446744073709551615 - tbl)) (Z_to_bv 64 0) (Z_to_bv 64 (40 * Z.of_nat n)) (Z_to_bv 64 (-1)) a7 x18 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 (base + 0x98)) fc None m (seg_rom segs)).
Proof. clear - w_7 w_8 w_12 w_21 w_26 w_27 w_45 GGOT4 GHASH4 GVDSO4 gTP gIMG_LO gIMG_HI LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_lh_entry_free gRDATA_LO CODE LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free segs base HIx. pose proof gLAYF0 as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOTU_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASHU_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_IMG_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GVDSO4_IMG as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GGOT4_GHASH4 as gL7_; unfold gw_le in gL7_. pose proof LAY_GHASH4x12_GVDSO4 as gL8_; unfold gw_le in gL8_. pose proof LAY_POS_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_. pose proof LAY_HI_e_fn_lh_entry_free as gL10_; unfold gw_le in gL10_.
induction k as [|k IH]; intros until tbl; intros Hk Hi Ht0 Htn MI SL.
all: pose proof (SL i ZSLOT (init_svs_nth_ge i n i ltac:(lia))) as C; unfold ent_addr, slot_cells, ZSLOT in C; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv] in C.
all: pose proof (munch_refl [(tbl, tbl + 40 * Z.of_nat n)] m) as MU; pose proof (wmono_refl segs m) as WM.
all: pose proof (munch_refl [(tbl + 40 * Z.of_nat i, tbl + 40 * Z.of_nat i + 40)] m) as MU2.
all: remember (tbl + 40 * Z.of_nat i) as B eqn:EB.
all: step; if_falsex. all: step; if_false.
all: step; rewrite <- EB. all: step.
all: stepz.
all: lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
assert (SL' : lh_slots segs mx tbl (init_svs (S i) n));
[ rewrite <- init_svs_step by lia; eapply (lh_slots_write_slot segs m _ tbl (init_svs i n) i ESLOT SL);
[rewrite init_svs_length; lia | unfold ent_addr; rewrite <- EB; exact MU2 | exact WM |];
unfold ent_addr, slot_cells, ESLOT; cbn [sv_k sv_kc sv_pad sv_v sv_nx sv_pv]; rewrite <- EB;
replace (Z_to_bv 64 LH_EMPTYv) with (Z_to_bv 64 18446744073709551615) by reflexivity; exact C |] end.
all: clear C MU2 SL; step.
- if_falsex. apply evt_done. do 2 eexists. split; [|split; [exact MU | split; [exact WM | split; [exact MI | ]]]].
+ replace (40 * Z.of_nat i + 40) with (40 * Z.of_nat n) by lia. reflexivity.
+ replace n with (S i) at 1 by lia. exact SL'.
- if_truex. replace (40 * Z.of_nat i + 40) with (40 * Z.of_nat (S i)) by lia.
eapply evt_cut.
{ eapply (IH (S i) n); [lia | lia | exact Ht0 | exact Htn | exact MI | exact SL']. }
cbv beta. intros ms' (m' & a7' & -> & MU' & WM' & MI' & SLn).
apply evt_done. exists m', a7'. split; [reflexivity|]. split; [|split; [|split; [exact MI' | exact SLn]]].
+ eapply munch_trans; [exact MU | exact MU'].
+ eapply wmono_trans; [exact WM | exact WM'].
Qed.

Notation lh_glob4 := (lh_glob segs S4F GHASH4 GGOT4 GVDSO4 vdso_ok4).

#[using="LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma lh_glob_client : forall LB SP m m', heap_pres S4L LB SP m m' -> lh_glob4 m -> lh_glob4 m'.
Proof. clear - LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOTU_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASHU_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_IMG_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GVDSO4_IMG as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GGOT4_GHASH4 as gL7_; unfold gw_le in gL7_. pose proof LAY_GHASH4x12_GVDSO4 as gL8_; unfold gw_le in gL8_. pose proof LAY_POS_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_. pose proof LAY_HI_e_fn_lh_entry_free as gL10_; unfold gw_le in gL10_.
intros LB SP m m' HPR ([seed G1] & G2 & (vf & G3 & VF)). split; [| split].
- exists seed. eapply (heap_pres_rw_cells S4L); [exact HPR | exact G1 |]. right; left. intros a Ha. cbn in Ha. gw_expose GHASH4.
cbn. gw_cs.
- eapply (heap_pres_rw_cells S4L); [exact HPR | exact G2 |]. right; left. intros a Ha. cbn in Ha. gw_expose GGOT4.
cbn. gw_cs.
- exists vf. split; [| exact VF]. eapply (heap_pres_rw_cells S4L); [exact HPR | exact G3 |]. right; left. intros a Ha. cbn in Ha. gw_expose GVDSO4.
cbn. gw_cs.
Qed.

Definition lh_table_new_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
lh_glob4 m' /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, lhtab2 segs S4F m' BS r [] /\ HEAPx A' (BS ++ LB) m' md') ).

#[using="w_7 w_8 w_12 w_21 w_26 w_27 w_45 hi_7 hi_26 lo_8 lo_27 joff_12 joff_21 joff_45 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER D_7 E_7 D_8 E_8 D_12 E_12 D_21 E_21 D_26 E_26 D_27 E_27 D_45 E_45 ANCH_8 ANCH_27 LINK_12 LINK_21 LINK_45 RNG_GGOT4 RNG_GHASH4 RNG_GVDSO4 LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free"] Lemma lh_kchar_table_new_cps :
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
lh_glob4 m ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP ->
bv_unsigned ra mod 2 = 0 ->
a0 = Z_to_bv 64 16 -> a1 = Z_to_bv 64 (fn_lh_entry_free S4F) ->
(forall ms' md', lh_table_new_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 lh_kchar_table_new_entry) fc None m (seg_rom segs)) md) T.
Proof. clear - w_7 w_8 w_12 w_21 w_26 w_27 w_45 hi_7 hi_26 lo_8 lo_27 joff_12 joff_21 joff_45 LAY_gIMG_LO LAY_TPLO LAY_TPHI gRDATA_LO CODE BASE4 BASER D_7 E_7 D_8 E_8 D_12 E_12 D_21 E_21 D_26 E_26 D_27 E_27 D_45 E_45 ANCH_8 ANCH_27 LINK_12 LINK_21 LINK_45 RNG_GGOT4 RNG_GHASH4 RNG_GVDSO4 LAY_GGOTU_GHASH4 LAY_GHASHU_GVDSO4 CS_GHASH4 CS_GGOT4 CS_GVDSO4 LAY_IMG_GGOT4 LAY_GVDSO4_IMG LAY_RDATA_GGOT4 LAY_GGOT4_GHASH4 LAY_GHASH4x12_GVDSO4 LAY_POS_e_fn_lh_entry_free LAY_HI_e_fn_lh_entry_free segs gTP S4F HIx. pose proof gLAYF as gLAYF_. pose proof LAY_TPLO as gL0_; unfold gw_le in gL0_. pose proof LAY_TPHI as gL1_; unfold gw_le in gL1_. pose proof LAY_GGOTU_GHASH4 as gL2_; unfold gw_le in gL2_. pose proof LAY_GHASHU_GVDSO4 as gL3_; unfold gw_le in gL3_. pose proof LAY_IMG_GGOT4 as gL4_; unfold gw_le in gL4_. pose proof LAY_GVDSO4_IMG as gL5_; unfold gw_le in gL5_. pose proof LAY_RDATA_GGOT4 as gL6_; unfold gw_le in gL6_. pose proof LAY_GGOT4_GHASH4 as gL7_; unfold gw_le in gL7_. pose proof LAY_GHASH4x12_GVDSO4 as gL8_; unfold gw_le in gL8_. pose proof LAY_POS_e_fn_lh_entry_free as gL9_; unfold gw_le in gL9_. pose proof LAY_HI_e_fn_lh_entry_free as gL10_; unfold gw_le in gL10_.
intros until errv. intros HP G ST LO LOS SPA HT ERR TP RA A0 A1 K.
unfold_consts. word_range sp SPR.
destruct G as ([seed G1] & G2 & (vf & G3 & VF)). gw_expose GHASH4. gw_expose GGOT4. gw_expose GVDSO4.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_pres_refl S4L LB (bv_unsigned sp) m) as HPR.
pose proof (wmono_refl segs m) as WM.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m) as MU.
apply rz_evt; [exact MOK|]. unfold lh_kchar_table_new_entry. subst a0 a1.
carve_frame 48%nat ST.
do 6 step.
step. step. step. step. step. step. step.

alloc_call (hi_calloc S4L HIx) S4L HIx HP MU WM MI.
intros ms2 m2 md2 A2 r e2 RS VM2 ST2 HPR2 ERR2 OUT2. open_ret RS. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP HPR2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in G1; [| right; left; intros q Hq; cbn in Hq; cbn; gw_cs]. cbn [hl_segs S4L] in G1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in G2; [| right; left; intros q Hq; cbn in Hq; cbn; gw_cs]. cbn [hl_segs S4L] in G2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in G3; [| right; left; intros q Hq; cbn in Hq; cbn; gw_cs]. cbn [hl_segs S4L] in G3.
clear MU WM MI ST.
destruct OUT2 as [(-> & HerrHP2 & HP2) | (Hr & BLK & HP2)].
-
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_truex. do 7 step.
apply evt_RZ_done. apply K. unfold lh_table_new_post.
exists m2, A2, 0, e2.
split; [| split; [exact VM2 | split; [| split; [exact HPR | split; [exact ERR2 | split; [| left; auto]]]]]].
+ apply ret_statew_same.
+ release_frame FR ST2 (bv_unsigned sp). exact ST2.
+ split; [exists seed; exact G1 | split; [exact G2 | exists vf; split; [exact G3 | exact VF]]].
-
change (Z.to_nat (1 * 56)) with 56%nat in BLK. change (1 * 56) with 56 in HP2. cbn [repeat] in BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
pose proof (heap_mem_inv _ _ _ _ _ _ HP2) as MI. cbn [hl_segs S4L] in MI.
pose proof (heap_blk S4L HIx _ _ _ _ r 56 HP2 ltac:(left; reflexivity)) as (_ & Hal & Hlo & Hhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ r 56 HP2 ltac:(left; reflexivity)) as Himg_r. cbn [hl_img_lo hl_img_hi S4L] in Himg_r.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hhi.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 56)] m2) as MU.
pose proof (wmono_refl segs m2) as WM.
reenter MOK2.
step. if_falsex. step. step. ubsan_align8 r.
stepz.
stepz.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mcnt end.
step. step. step. step.

alloc_call (hi_calloc S4L HIx) S4L HIx HP2 MU WM MI.
intros ms3 m3 md3 A3 q e3 RS3 VM3 ST3 HPR3 ERR3 OUT3. open_ret RS3. cbn [hl_segs S4L] in *.
extend_pres S4L HIx HPR MU WM HP2 HPR3.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in BLK; [| eapply client_range_block; [left; reflexivity | lia | cbn; lia]]. cbn [hl_segs S4L] in BLK.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in G1; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in G2; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR3) in G3; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G3.
clear MU WM MI ST2.
destruct OUT3 as [(-> & HerrHP3 & HP3) | (Hq & BLK2 & HP3)].
+
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 56)] m3) as MU.
pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. step. stepz. step. if_true. step.

alloc_call (hi_free S4L HIx) S4L HIx HP3 MU WM MI.
{ right. exists 56. left. reflexivity. }
intros ms5 m5 md5 A5 r5 RS5 VM5 ST5 HPR5 ERR5 HP5. open_ret RS5. cbn [hl_segs S4L] in *.
rewrite lb_remove_head in HPR5, HP5.
extend_pres S4L HIx HPR MU WM HP3 HPR5.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in FR; [| left; cbn; lia]. cbn [hl_segs S4L] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in G1; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G1.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in G2; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G2.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR5) in G3; [| right; left; intros z Hz; cbn in Hz; cbn; gw_cs]. cbn [hl_segs S4L] in G3.
clear MU WM MI ST3 BLK.
pose proof (heap_model_ok _ _ _ _ _ _ HP5) as MOK5.
pose proof (heap_mem_inv _ _ _ _ _ _ HP5) as MI. cbn [hl_segs S4L] in MI.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)] m5) as MU.
pose proof (wmono_refl segs m5) as WM.
reenter MOK5.
do 8 step.
apply evt_RZ_done. apply K. unfold lh_table_new_post.
exists m5, A5, 0, e3.
split; [| split; [| split; [| split; [exact HPR | split; [exact ERR5 | split; [| left; auto]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; [| exact VM5]. eapply model_vm_only_trans; eassumption.
* release_frame FR ST5 (bv_unsigned sp). exact ST5.
* split; [exists seed; exact G1 | split; [exact G2 | exists vf; split; [exact G3 | exact VF]]].
+
change (16 * 40) with (40 * 16) in HP3. change (16 * 40) with (40 * Z.of_nat 16) in BLK2.
pose proof (heap_model_ok _ _ _ _ _ _ HP3) as MOK3.
pose proof (heap_mem_inv _ _ _ _ _ _ HP3) as MI. cbn [hl_segs S4L] in MI.
destruct (blocks2 S4L HIx _ _ _ _ _ _ _ _ HP3) as ((Hqal & Hqlo & Hqhi & Hqimg) & _ & Hdj).
cbn [hl_img_lo hl_img_hi S4L] in Hqimg. unfold alloc_ceiling, sp_window_lo, stack_max_size in Hqhi.
pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp); (r, r + 56); (q, q + 640)] m3) as MU.
pose proof (wmono_refl segs m3) as WM.
reenter MOK3.
step. step. step. step. if_falsex.
step. step. step. stepz. step.
step. if_false. step. step. ub_notltu q 0. step. rewrite (unsigned_lit q), (land7_of_mod8 q) by (first [lia | mod8_tac]). step. step. step.

lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
pose proof (zeros_slots segs 16 mx q BLK2) as SL0 end.
rewrite <- init_svs_0 in SL0. clear BLK2.
replace (Z_to_bv 64 0) with (Z_to_bv 64 (40 * Z.of_nat 0)) at 2 by (f_equal; lia).
replace 640 with (40 * Z.of_nat 16) by reflexivity.
call (lh_init_loop 15 0 16); [reflexivity | lia | lia | lia | | exact SL0 |]. { assumption. }
match goal with H : lh_slots segs _ q (init_svs 16 16) |- _ => rename H into SL16 end.
do 8 step.
apply evt_RZ_done. apply K. unfold lh_table_new_post.
match goal with |- context [MS _ _ _ _ _ ?mf _] => exists mf, A3, r, e3 end.
assert (HP3' : HEAPx A3 ((r, 56) :: (q, 40 * 16) :: LB) m3 md3) by (eapply heap_perm; [exact HP3 | apply perm_swap]).
split; [| split; [| split; [| split; [ | split; [ eassumption | split; [| right]]]]]].
* apply ret_statew_same.
* eapply model_vm_only_trans; eassumption.
* release_frame FR ST3 (bv_unsigned sp). exact ST3.
* eapply heap_pres_trans; [exact HPR|].
lazymatch goal with |- heap_pres _ _ _ _ ?mf =>
match goal with MUx : munch _ m3 mf, WMx : wmono segs m3 mf |- _ =>
eapply (heap_pres_of_munch S4L LB (bv_unsigned sp)); [exact MUx | exact WMx |];
eapply (client_outside S4L HIx); [exact HP3' | intros b Hb; right; right; exact Hb | clia |];
solve_clientW S4L HIx HP3' end end.
* split; [eexists; eassumption | split; [eassumption | exists vf; split; [eassumption | exact VF]]].
* split; [exact Hr|]. exists [(r, 56); (q, 40 * 16)]. split.
-- exists q, 16, [], (init_svs 16 16). split; [reflexivity|]. split; [reflexivity|].
split; [| split; [exact SL16 | split; [| split; [constructor | split; [cbn; tauto | split; [cbn; lia | rewrite init_svs_length; lia]]]]]].
++ unfold lh_hdr, lh_hdrf. cbn [length Z.of_nat hd_of tl_of].
match goal with H : rw_cells segs _ r (?c1 :: ?c2 :: ?c3 :: ?rest) |- _ =>
apply (rw_cells_recast_prefix segs _ r [c1; c2; c3] [C4 (Z_to_bv 64 16); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] rest) in H;
[ cbn [app] in H; exact H | cbn; repeat split; reflexivity | vm_compute; reflexivity | reflexivity ] end.
++ split; [| split; [| split; [constructor | intros e He; destruct He]]].
** intros j e E. destruct j; discriminate.
** intros i sv E _. rewrite init_svs_all in E. apply nth_error_In in E. apply repeat_spec in E. subst sv. left. reflexivity.
-- cbn [app]. lazymatch goal with |- HEAP _ _ _ _ ?mf _ =>
match goal with MUx : munch _ m3 mf, WMx : wmono segs m3 mf, MIx : mem_inv segs mf |- _ =>
eapply (heap_frame S4L HIx); [exact HP3' | | exact WMx | exact MIx];
eapply (frame_writes_ok S4L HIx _ _ _ _ _ _ HP3' MUx); solve_frameW_with HP3' end end.
Qed.
End LhNew.

End RC__1.

End G.
End Mq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH QmZZ QKQo Q6WR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QsjA QEpW QZDE QbVh QlEo QWxq Q8Q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq7.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QsjA QEpW QZDE QbVh QlEo QWxq QXup Q5Rg.
Import QCcH QfLs Q0Ek QjDH.Mq0 QmZZ Q8tj QKQo.
Import QSL3.
Import Q8Q3.
Import QnCn.Mq0.
Import Q6WR.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.

Lemma upd_app_len' : forall {X} (a b : list X) x y, upd (a ++ x :: b) (length a) y = a ++ y :: b.
Proof. intros X a. induction a as [|z a IH]; intros b x y; cbn; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma nth_error_app_len : forall {X} (a b : list X) x, nth_error (a ++ x :: b) (length a) = Some x.
Proof. intros. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

Lemma firstn_app_len : forall {X} (a b : list X), firstn (length a) (a ++ b) = a.
Proof. intros. rewrite firstn_app, Nat.sub_diag, firstn_all. cbn. apply app_nil_r. Qed.

Lemma Forall_repeat0 : forall n, Forall (fun p : Z => p = 0) (repeat 0 n).
Proof. induction n; cbn; constructor; auto. Qed.

Ltac hperm := unfold lh_blocks, kblk, blk; perm.

Section WithSegs.
Variable segs : list Segment.
Variable fn : fnaddrs.
Notation wz := (Z_to_bv 64) (only parsing).

#[using="Type"] Lemma zobjc_hdr : forall m x q kids XBS,
zobjc segs fn m x q kids XBS -> List.NoDup (map blk_addr XBS) ->
exists pb cf, In (x, 48) XBS /\
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz cf)]) /\
(forall m' q', rw_cells segs m' x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q' ++ [C8 (wz cf)]) ->
agree_on segs (others x XBS) m m' -> zobjc segs fn m' x q' kids XBS).
Proof.
intros m x q kids XBS (t & tbl & size & es & svs & pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK) ND.
exists pb, t. split; [rewrite EX; left; reflexivity|]. split; [exact HDR|].
intros m' q' HDR' AG. exists t, tbl, size, es, svs, pb, PBS, KBS, esk, esz.
split; [exact Ees|]. split; [exact Lz|]. split; [exact Fz|]. split; [exact EX|]. rewrite EX in ND, AG.
split; [| split; [exact HDR' | split]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; right; exact Hb]].
- eapply lh_open_agree; [exact OPEN | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]].
- eapply okids_agree; [exact OK | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb]].
Qed.

#[using="Type"] Lemma zarrc_hdr : forall m x q kids XBS,
zarrc segs fn m x q kids XBS -> List.NoDup (map blk_addr XBS) ->
exists pb cf, In (x, 48) XBS /\
rw_cells segs m x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q ++ [C8 (wz cf)]) /\
(forall m' q', rw_cells segs m' x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q' ++ [C8 (wz cf)]) ->
agree_on segs (others x XBS) m m' -> zarrc segs fn m' x q' kids XBS).
Proof.
intros m x q kids XBS (a & arr & size & pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK) ND.
exists pb, a. split; [rewrite EX; left; reflexivity|]. split; [exact HDR|].
intros m' q' HDR' AG. exists a, arr, size, pb, PBS, KBS, ps.
split; [exact EX|]. rewrite EX in ND, AG.
split; [| split; [exact HDR' | split]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; right; exact Hb]].
- eapply alist_agree; [exact AL | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; left; exact Hb]].
- eapply okids_agree; [exact OK | exact AG | eapply (incl_others_tail x 48 _ PBS); [exact ND | intros b Hb; apply in_or_app; left; apply in_or_app; right; exact Hb]].
Qed.

#[using="Type"] Lemma zobj_last : forall m x q kids k nz t tbl size es svs XBS,
zobj segs fn m x q (kids ++ [k]) nz t tbl size es svs XBS ->
exists pb PBS KBS1 bs esk1 e esz,
es = esk1 ++ e :: esz /\ length esk1 = length kids /\ length esz = nz /\ Forall (fun e => le_v e = 0) esz /\
XBS = ((x, 48) :: lh_blocks t tbl size es ++ (concat KBS1 ++ bs)) ++ PBS /\
opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz t)]) /\
lh_open segs fn m t tbl size es svs /\
okids segs fn m kids (map le_v esk1) KBS1 /\
match k with None => le_v e = 0 /\ bs = [] | Some c => le_v e <> 0 /\ jval segs fn c m bs (le_v e) 1 end.
Proof.
intros m x q kids k nz t tbl size es svs XBS (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 L2]. rewrite length_map, length_app in L1. cbn in L1.
destruct (snoc_inv_gen esk) as [-> | (esk1 & e & ->)]; [cbn in L1; lia|].
rewrite map_app in OK. cbn [map] in OK.
destruct (okids_snoc_inv _ _ _ _ _ _ _ OK) as (vs1 & v & KBS1 & bs & Evs & -> & OK1 & Hk).
apply app_inj_last in Evs as [<- <-].
exists pb, PBS, KBS1, bs, esk1, e, esz.
rewrite length_app in L1. cbn in L1.
split; [rewrite Ees, <- app_assoc; reflexivity|]. split; [lia|]. split; [exact Lz|]. split; [exact Fz|].
split; [rewrite EX, concat_snoc; reflexivity|].
split; [exact OPB|]. split; [exact HDR|]. split; [exact OPEN|]. split; [exact OK1 | exact Hk].
Qed.

#[using="Type"] Lemma zobj_last_close : forall m m' x q kids nz t tbl size esk1 e esz svs' pb PBS KBS1,
length esz = nz -> Forall (fun e => le_v e = 0) esz ->
opt_pbuf segs m PBS pb ->
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz t)]) ->
okids segs fn m kids (map le_v esk1) KBS1 ->
lh_open segs fn m' t tbl size (esk1 ++ with_v e 0 :: esz) svs' ->
agree_on segs ((x, 48) :: concat KBS1 ++ PBS) m m' ->
zobj segs fn m' x q kids (S nz) t tbl size (esk1 ++ with_v e 0 :: esz) svs'
(((x, 48) :: lh_blocks t tbl size (esk1 ++ with_v e 0 :: esz) ++ concat KBS1) ++ PBS).
Proof.
intros m m' x q kids nz t tbl size esk1 e esz svs' pb PBS KBS1 Lz Fz OPB HDR OK OPEN AG.
exists pb, PBS, KBS1, esk1, (with_v e 0 :: esz).
split; [reflexivity|]. split; [cbn; lia|]. split; [apply Forall_cons; [reflexivity | exact Fz]|]. split; [reflexivity|].
split; [| split; [| split; [exact OPEN|]]].
- eapply opt_pbuf_agree; [exact OPB | exact AG | intros b Hb; right; apply in_or_app; right; exact Hb].
- eapply rw_cells_agree; [exact HDR | exact AG | exists x, 48; split; [left; reflexivity | cbn; lia]].
- eapply okids_agree; [exact OK | exact AG | intros b Hb; right; apply in_or_app; left; exact Hb].
Qed.

#[using="Type"] Lemma zobj_nil_vals : forall m x q nz t tbl size es svs XBS,
zobj segs fn m x q [] nz t tbl size es svs XBS -> forall e, In e es -> le_v e = 0.
Proof.
intros m x q nz t tbl size es svs XBS (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK) e He.
pose proof (okids_len _ _ _ _ _ _ OK) as [L1 _]. rewrite length_map in L1. destruct esk; [| cbn in L1; discriminate].
subst es. cbn in He. exact (proj1 (Forall_forall _ _) Fz e He).
Qed.

#[using="Type"] Lemma zarr_nil_vals : forall m x q nz a arr size XBS,
zarr segs fn m x q [] nz a arr size XBS ->
exists pb PBS, XBS = [(x, 48); (a, 32); (arr, 8 * size)] ++ PBS /\ opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_ARRAY 0 (fn_arr_to_json_string fn) pb 0 q ++ [C8 (wz a)]) /\
alist segs fn m [(a, 32); (arr, 8 * size)] a (repeat 0 nz).
Proof.
intros m x q nz a arr size XBS (pb & PBS & KBS & ps & EX & OPB & HDR & AL & OK).
destruct (okids_nil_inv _ _ _ _ _ OK) as [-> ->]. exists pb, PBS. cbn [concat app] in EX.
split; [exact EX|]. split; [exact OPB|]. split; [exact HDR | exact AL].
Qed.

#[using="Type"] Lemma zobj_nil_shape : forall m x q nz t tbl size es svs XBS,
zobj segs fn m x q [] nz t tbl size es svs XBS ->
exists pb PBS, XBS = ((x, 48) :: lh_blocks t tbl size es) ++ PBS /\ opt_pbuf segs m PBS pb /\
rw_cells segs m x (jhdr_cells JT_OBJECT 0 (fn_obj_to_json_string fn) pb 0 q ++ [C8 (wz t)]) /\
lh_open segs fn m t tbl size es svs /\ (forall e, In e es -> le_v e = 0) /\ length es = nz.
Proof.
intros m x q nz t tbl size es svs XBS Z0. pose proof (zobj_nil_vals _ _ _ _ _ _ _ _ _ _ Z0) as VZ.
destruct Z0 as (pb & PBS & KBS & esk & esz & Ees & Lz & Fz & EX & OPB & HDR & OPEN & OK).
destruct (okids_nil_inv _ _ _ _ _ OK) as [E1 ->]. destruct esk; [| cbn in E1; discriminate]. subst es.
exists pb, PBS. cbn [concat app] in EX. rewrite app_nil_r in EX.
split; [exact EX|]. split; [exact OPB|]. split; [exact HDR|]. split; [exact OPEN|]. split; [exact VZ | cbn; exact Lz].
Qed.

End WithSegs.
End Mq7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq8.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi Qsw7 QJjn.
Import UPIU.Mqg.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1.
Open Scope Z_scope.
Import Q6q3.
Import Q0Hd.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.CodeAt OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGen OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.StepGenX2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwCallee OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply2 OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApplyJ.
Local Ltac step_core segs R F pc fc rv m ro ::= sg_step_core; gwj_pc_norm. Local Ltac mkr__step_core_0 segs R F pc fc rv m ro := sg_step_core; gwj_pc_norm.
Local Ltac zstep ::= sg_zstep; gwj_pc_norm. Local Ltac mkr__zstep_1 := sg_zstep; gwj_pc_norm.
Local Ltac post_call segs m ::= g_post_call segs m. Local Ltac mkr__post_call_2 segs m := g_post_call segs m.

Definition toknew_code (w_0 w_1 : Z) : list Z :=
[w_0; w_1]%Z.

Local Ltac if_true ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ]. Local Ltac mkr__if_true_3 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with true; [cbv iota| symmetry; solve_cond] end | if_truex ].
Local Ltac if_false ::= first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ]. Local Ltac mkr__if_false_4 := first [ lazymatch goal with |- evt ?segs ?Q (MS ?R ?F (if ?c then ?a else ?b) ?fc ?rv ?m ?ro) => replace c with false; [cbv iota| symmetry; solve_cond] end | if_falsex ].

Local Ltac reenter MOK ::= apply rz_evt; [ exact MOK |]; try g_ret_pc. Local Ltac mkr__reenter_5 MOK := apply rz_evt; [ exact MOK |]; try g_ret_pc.

Section G.
Variables (segs : list Segment) (base : Z).
Variables (w_0 w_1 : Z).
Variables (joff_1 : bv 21).
Variables (e_1411c : Z).
Context {RC__ : Q6q3.RunConsts}.
Variables (e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC : Z) (gVOL gCS : Z -> Prop) (gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI : Z).
Hypothesis gH1 : forall a, gCS a -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH2 : gl_range_ok gIMG_LO gIMG_HI.
Hypothesis gH3 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis gH4 : forall a, (gTP - 164 <= a < gTP - 160)%Z -> ~ gCS a.
Hypothesis gH5 : forall c a, In c [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))] -> (fst c <= a < fst c + Z.of_nat (length (snd c)))%Z ->
~ gCS a /\ ~ (gTP - 164 <= a < gTP - 160)%Z /\ (gIMG_LO <= a < gIMG_HI)%Z.
Hypothesis LAY_gIMG_LO : (gIMG_LO = 65536)%Z.
Hypothesis LAY_TPLO : gw_le gIMG_LO (gTP - 164).
Hypothesis LAY_TPHI : gw_le (gTP - 160) gIMG_HI.
#[using="gH2 gH3 LAY_gIMG_LO"] Lemma gLAYF : ((0 <= gIMG_LO /\ gIMG_HI <= alloc_ceiling) /\ (gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Proof. pose proof gH2 as X2; unfold gl_range_ok in X2. split; [exact X2|]. split; [|exact LAY_gIMG_LO]. pose proof (gH3 (gTP - 164)%Z); pose proof (gH3 (gTP - 161)%Z); lia. Qed.
Definition gLAYF0 : Prop := ((gIMG_LO <= gTP - 164 /\ gTP - 160 <= gIMG_HI) /\ gIMG_LO = 65536)%Z.
Variables (e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free : Z).
Hypothesis CODE : code_at segs base (toknew_code w_0 w_1).
Hypothesis BASE4 : gw_b4 base.
Hypothesis BASER : gw_br base 8.
Hypothesis D_1 : decode_any (Z_to_bv 32 w_1) = Some (Jal 0 joff_1, 4%Z).
Hypothesis E_1 : is_ecall (Z_to_bv 32 w_1) = false.
Hypothesis LINK_1 : gw_anch (base + 4 + bv_signed joff_1)%Z (e_1411c + 0)%Z.

Hypothesis rw_cells_recast : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@UPIU.Mqg.gw_all) (@UPIU.Mqg.rw_cells_recast) (base + 7104)%Z)) in let T := eval cbv beta delta [UPIU.Mqg.printbuf_new_entry] in T in let T := gw_fold_pcs T base (7104)%Z [0; 28; 52; 80]%Z in exact T).
Hypothesis printbuf_new_cps : gw_hyp ltac:(let T := constr:(ltac:(gw_callee_ty2 (@UPIU.Mqg.gw_all) (@UPIU.Mqg.printbuf_new_cps) (base + 7104)%Z)) in let T := eval cbv beta delta [UPIU.Mqg.printbuf_new_entry] in T in let T := gw_fold_pcs T base (7104)%Z [0; 28; 52; 80]%Z in exact T).

Let S4L : heap_layout :=
{| hl_segs := segs;
hl_malloc := e_malloc; hl_free := e_free; hl_calloc := e_calloc; hl_realloc := e_realloc; hl_malloc2 := e_malloc2; hl_free2 := e_free2;
hl_tp := gTP;
hl_got_guard := gGOTG; hl_guard := gGUARD; hl_auxv := gAUXV; hl_libc := gLIBC; hl_volatile := gVOL;
hl_stack := 8256;
hl_client_static := gCS;
hl_scratch := fun a => (gTP - 164 <= a < gTP - 160)%Z;
hl_consts := [(gHEXGOT, le8 (Z_to_bv 64 gHEXPTR)); (gHEXPTR, le8 (Z_to_bv 64 gHEXCHARS))];
hl_img_lo := gIMG_LO; hl_img_hi := gIMG_HI;
hl_static_in_img := gH1; hl_img_range := gH2; hl_scratch_in_img := gH3; hl_scratch_not_static := gH4; hl_consts_ok := gH5 |}.
Let S4F : fnaddrs := {| fn_obj_to_json_string := e_fn_obj_to_json_string; fn_arr_to_json_string := e_fn_arr_to_json_string; fn_bool_to_json_string := e_fn_bool_to_json_string; fn_dbl_to_json_string := e_fn_dbl_to_json_string; fn_int_to_json_string := e_fn_int_to_json_string; fn_str_to_json_string := e_fn_str_to_json_string; fn_ud_to_json_string := e_fn_ud_to_json_string; fn_free_userdata := e_fn_free_userdata; fn_lh_entry_free := e_fn_lh_entry_free; fn_lh_char_hash := e_fn_lh_char_hash; fn_lh_char_equal := e_fn_lh_char_equal; fn_arr_entry_free := e_fn_arr_entry_free |}.
#[using="w_0 w_1 joff_1 e_1411c RC__ e_malloc e_free e_calloc e_realloc e_malloc2 e_free2 gTP gGOTG gGUARD gAUXV gLIBC gVOL gCS gHEXGOT gHEXPTR gHEXCHARS gIMG_LO gIMG_HI gH1 gH2 gH3 gH4 gH5 LAY_gIMG_LO LAY_TPLO LAY_TPHI e_fn_obj_to_json_string e_fn_arr_to_json_string e_fn_bool_to_json_string e_fn_dbl_to_json_string e_fn_int_to_json_string e_fn_str_to_json_string e_fn_ud_to_json_string e_fn_free_userdata e_fn_lh_entry_free e_fn_lh_char_hash e_fn_lh_char_equal e_fn_arr_entry_free CODE BASE4 BASER D_1 E_1 LINK_1 rw_cells_recast printbuf_new_cps S4F"] Lemma gw_all : True. Proof. exact I. Qed.
Local Tactic Notation "gj_rv" ident(h) := try revert h.

Ltac g_ra_even := lazymatch goal with |- (bv_unsigned (Z_to_bv 64 (?b + ?k)) mod 2 = 0)%Z =>
let X := fresh in let Y := fresh in pose proof BASE4 as X; pose proof BASER as Y; unfold gw_b4, gw_br in X, Y; rewrite unsigned_lit by lia; Z.div_mod_to_equations; lia end.
Ltac alloc_side ::=
try (progress fold S4L); try (progress fold S4F);
simpl hl_segs; simpl hl_stack; simpl hl_tp; simpl hl_malloc; simpl hl_free; simpl hl_calloc; simpl hl_realloc;
rewrite ?unsigned_lit by lia;
lazymatch goal with
| |- forall _, _ => idtac
| |- _ \/ _ => idtac
| |- (bv_unsigned (Z_to_bv 64 (_ + _)) mod 2 = 0)%Z => first [ g_ra_even | lia ]
| |- _ =>
lazymatch goal with
| |- stk _ _ _ _ => eassumption
| |- rw_cells _ _ _ _ => eassumption
| |- @eq (bv _) _ _ => first [ reflexivity | eassumption | symmetry; eassumption | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
| |- (_ mod 16 = 0)%Z =>
first [ assumption
| match goal with H : (bv_unsigned ?sp mod 16 = 0)%Z |- ((bv_unsigned ?sp + ?k) mod 16 = 0)%Z =>
rewrite <- Zplus_mod_idemp_l, H; reflexivity end
| lia ]
| |- _ => first [ lia | unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia ]
end end.
Ltac gj_fold := try (progress fold S4L); repeat match goal with H : _ |- _ => progress fold S4L in H end; try (progress fold S4F); repeat match goal with H : _ |- _ => progress fold S4F in H end.
Ltac unfold_consts ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *.
Ltac clia ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size in *; lia.
Ltac unfold_consts_goal ::= gj_fold; unfold alloc_ceiling, sp_window_lo, stack_max_size.

Section RC__1.

Section TokNew.
Variable HIx : heap_iface S4L.
Notation HEAPx := (HEAP S4L HIx).

Definition json_tokener_new_entry : Z := (base + 0x0).

Definition tstack_of_zeros : Prop := forall m k A,
rw_cells segs m A [CB (32 * k)%nat (repeat (Z_to_bv 8 0) (32 * k))] ->
tstack segs m A (repeat lvl_zero k).

Definition lb_remove_notin : Prop := forall p LB, (forall n, ~ In (p, n) LB) -> lb_remove p LB = LB.
Definition lb_remove_zero : Prop := forall A LB m md, HEAPx A LB m md -> lb_remove 0 LB = LB.

Definition tok_cells0 : list cell :=
[C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C1 (Z_to_bv 8 0); CB 7 (repeat (Z_to_bv 8 0) 7);
C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)].
Definition lvl_cells0 : list cell := [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

Definition toknew_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
(m : word -> option byte) (md : Model) (LB : list blk) (lo : Z)
(ms' : machine_state) (md' : Model) : Prop :=
exists m' (A' : AS S4L HIx) (r : Z) (errv' : word),
ret_statew S4L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (Z_to_bv 64 r) m' ms' /\
model_vm_only md md' /\
stk segs m' lo (bv_unsigned sp) /\
heap_pres S4L LB (bv_unsigned sp) m m' /\
rw_cells segs m' (gTP - 164) [C4 errv'] /\
( (r = 0 /\ HEAPx A' LB m' md')
\/ (r <> 0 /\ exists BS, tok_fresh segs m' BS r /\ HEAPx A' (BS ++ LB) m' md') ).

Definition json_tokener_new_cps : Prop :=
forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (md : Model) (T : TSet)
(A : AS S4L HIx) (LB : list blk) (lo : Z) (errv : word),
HEAPx A LB m md ->
stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 48 - 16 - 8256 ->
bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= hi_top S4L HIx ->
rw_cells segs m (gTP - 164) [C4 errv] ->
tp = Z_to_bv 64 gTP -> bv_unsigned ra mod 2 = 0 ->
(forall ms' md', toknew_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m md LB lo ms' md' ->
realizes segs (mkCfg ms' md') T) ->
realizes segs (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 json_tokener_new_entry) fc None m (seg_rom segs)) md) T.
End TokNew.

End RC__1.

End G.
End Mq8.
