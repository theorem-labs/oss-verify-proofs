(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup UEQM Lib.GwApply QWxq QRjH QHnV QCcH QfLs Q0Ek Qtgi QjDH UC8c Qsw7 QJjn QRUw QkMG UG8z Udyh U2Sr ULbz UIsM UXfU UdFq UX85 Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq0 QkMG.
Import UG8z Udyh.Mq0 U2Sr ULbz UIsM.Mq2 UXfU.Mq0.
Import UdFq UX85.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeNumErrX.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Let LB0 : list blk := LB0 pf LBc.

#[using="Type"] Lemma num_err_sw_at :
forall (pc : Z) (ts : tstate) (e : Z) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word) (cop : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
(pc = 0x23e2c \/ pc = 0x23e48) ->
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
0 <= e < 2^32 ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
KOUT7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf pc cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 e) s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros Hpc STC INV He TDOK FS FRM KOUT.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR.
unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
assert (INtk : In (tk, 72) (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0)) by (unfold pe_blocks; apply in_or_app; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (wmono_refl rsegs m) as WM.
pose proof (munch_refl [(tk, tk + 72); (spf, spf + PE_FRAME)] m) as MU.
stash PB. stash TSK. stash REST. clear HP.
apply rz_evt; [exact MOK|].
destruct Hpc as [-> | ->]; step; step.
all: unstash PB; unstash TSK; unstash REST.
all: apply evt_RZ_done.
all: eapply (KOUT (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 e) ucs high quote) obj objs objbs) []); [ | tdok TDOK | exact FS | exact FRM].
all: apply (PE_INV_W HIx).
all: eapply (PE_INV_retok HIx) with (ts := ts0); [exact STC | exact INV | exact MU | exact WM | assumption | | cbn; lia | reflexivity | ].
all: try (unfold ts0, tok_cells, tok_cells_g; cbn [t_pb t_depth ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_mxd]; assumption).
all: unfold ts0, pe_frame; cbn [t_obj pf_spf pf_mxd]; exact FR.
Qed.

#[using="Type"] Lemma num_err_sw28 :
forall (ts : tstate) (e : Z) (m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word) (cop : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 s8 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
0 <= e < 2^32 ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
KOUT7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x23e48 cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 e) s6 s7 s8 s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof. intros. eapply num_err_sw_at; [right; reflexivity | eassumption .. ]. Qed.
End PeNumErrX.

End RC__1.
End Mq0.
From Stdlib Require Sorting.Permutation.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT8C UV3d. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4Eu Uc8V UvXs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3 Require Tk3Tac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import QXup.
Import UEQM.
Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge QWxq.Mq0.
Import QRjH.
Import QHnV QCcH QfLs Q0Ek Qtgi QjDH QjDH.Mq0.
Import UC8c.Mq0.
Import Qsw7 QJjn QRUw.Mq0.
Import UT8C UV3d.
Import QkMG.
Import UG8z Udyh.Mq0 U2Sr ULbz UIsM.Mq2 UXfU.Mq0.
Import QJjn.Mq0.
Import QgoP.
Import U4Eu.
Import Uc8V.
Import UdFq UvXs UX85 UX85.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Import Q6q3. Import TopUbTac Tk1Tac Tk3Tac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma numb_not_in_b0' : forall bs, Forall (fun b => numb b = true) bs -> ~ In b0 bs.
Proof.
intros bs H Hin. apply Forall_forall with (x := b0) in H; [| exact Hin]. unfold numb, numch in H. change (bv_unsigned b0) with 0 in H. cbn in H. discriminate.
Qed.

Section PeNumUint.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis STRTOULL : strtox_stmt strtoull_entry.
Let LB0 : list blk := LB0 pf LBc.

#[using="STRTOULL"] Lemma num_uint :
forall (n : nat) (ts : tstate) (l : tlevel) (txt : list byte)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word) (cop : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
pbufc rsegs m (t_pbs ts) (t_pb ts) txt -> Forall (fun b => numb b = true) txt -> Z.of_nat (length txt) <= pf_len pf ->
sx32 (ts_isd (t_x ts)) = Z_to_bv 64 0 ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
(mbase pf ts + 8 <= n)%nat ->
KALL HIx pf q LBc payload me lo sv T F0 n -> KOUT7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x22e88 cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
s4 (Z_to_bv 64 (t_pb ts)) s7 (Z_to_bv 64 (pf_sb pf + t_co ts)) s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst PBC NUM LTXT SX0 Hco Hcb TDOK FS FRM Hn KALL KOUT.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold mbase in Hn. cbn [pf_len t_co pf_mxd] in Hn.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (LBall := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) in *.
assert (INtk : In (tk, 72) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ tk 72 HP INtk) as Himg_t. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_t.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi.

pose proof PBC as (buf & bpos & cap & post & Epbs & Ltxt & PCORE). pose proof PCORE as (Hbpos & Hcap & Hclen & PBS & PBUF). cbn [hl_segs S4L pf_mxd] in PBS, PBUF.
assert (INpb : In (pb, 16) LBall) by (unfold LBall, pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
assert (INbuf : In (buf, cap) LBall) by (unfold LBall, pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ pb 16 HP INpb) as Himg_pb. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_pb.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & Hbufal & Hbuflo & Hbufhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ buf cap HP INbuf) as Himg_buf. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_buf.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi, Hbufhi.
rewrite !length_app in Hclen. cbn [length pf_mxd] in Hclen.
assert (TXT0 : bytes_at rsegs m buf (txt ++ [b0])).
{ pose proof (rw_cells_bytes_at' _ _ _ _ PBUF) as X. cbn [cells_bytes cbytes pf_mxd] in X. rewrite app_nil_r in X.
rewrite app_assoc in X. apply bytes_at_app in X. exact (proj1 X). }

destruct (nth_error (txt ++ [b0]) 0) as [c0|] eqn:Hc0; [| apply nth_error_None in Hc0; rewrite length_app in Hc0; cbn in Hc0; lia].
pose proof (string_byte m buf _ 0 c0 TXT0 Hc0 ltac:(lia)) as RD0. rewrite Z.add_0_r in RD0.
pose proof (bv_unsigned_in_range 8 c0) as C0R. unfold bv_modulus in C0R. cbn in C0R.

pose proof (heap_canary S4L HIx _ _ _ _ HP) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard hl_segs S4L pf_mxd] in CAN1, CAN2.
pose proof (pe_frame_split_ret _ _ _ _ _ _ _ _ FR) as (FRobj & (wa & wb & Ej1 & FRa & FRb) & FRrest). unfold pe_frame_rest in FRrest.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
change (0x77c00 - 164) with 490332 in ERR.
assert (USPF : bv_unsigned (Z_to_bv 64 spf) = spf) by (apply unsigned_lit; lia).
stash PB. stash TSK. stash REST. stash LV. clear HPR OBJ.
apply rz_evt; [exact MOK|].
tk3_walk 0 ltac:(try change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0))).
destruct (Z.eq_dec (bv_unsigned c0) 45) as [C45 | N45].
{
first [if_truex | if_falsex]. tk3_walk 0x23e48 idtac. unstash PB. unstash TSK. unstash REST. unstash LV.
apply evt_RZ_done.
eapply (num_err_sw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 ts0 7); [exact STC | exact INV | lia | tdok TDOK | exact FS | exact FRM | exact KOUT]. }
first [if_truex | if_falsex]. tk3_walk 0x29030 idtac.

pose proof (munch_refl [(spf - 416, spf); (spf + 8, spf + 8 + 8); (490332, 490336)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
stash TOK.
pose proof (json_parse_uint64_spec STRTOULL) as PU. unfold parse_i64_stmt in PU.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [ eapply PU with (SP := spf) (A := buf) (R := spf + 8) (lo := lo) (str := txt)
| unfold parse_i64_post, parse_i64_W; post_call segs mm ] end.
all: clear PU.
1:{ exact USPF. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact TXT0. } 1:{ apply numb_not_in_b0'; exact NUM. } 1:{ lia. } 1:{ lia. }
1:{ exact FRa. } 1:{ lia. } 1:{ lia. } 1:{ clear - SPA. Z.div_mod_to_equations; lia. } 1:{ exact ERR. } 1:{ reflexivity. } 1:{ exact CAN1. } 1:{ exact CAN2. } 1:{ exact ST. }
1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ vm_compute; reflexivity. } 1:{ exact MI. }
cbv beta. change (0x77c00 - 164) with 490332 in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end. rename MU into MU1. rename WM into WM1.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
match goal with H : stk rsegs m1 lo _ |- _ => rename H into ST1 end.
match goal with H : rw_cells rsegs m1 (spf + 8) [C8 ?v] |- _ => rename H into FRa1 end.
match goal with H : rw_cells rsegs m1 490332 [C4 ?e] |- _ => rename H into ERR1 end.
match goal with H : ?rv = 0 \/ ?rv = 1 |- _ => rename H into HRV end.
lazymatch type of FRa1 with rw_cells _ _ _ [C8 ?vv] => rename vv into vret end.
lazymatch type of ERR1 with rw_cells _ _ _ [C4 ?ee] => rename ee into eret end.
unstash TOK. unstash PB. unstash TSK. unstash REST. unstash LV.
destruct (PE_INV_stackcall HIx _ _ _ _ _ _ m m1 _ _ ts0 cb cb j1 (le8 vret ++ le8 wb) j2 utf utf sv errv eret _ STC INV MU1 WM1 MI1) as [INV1 HPRs];
[ apply Forall_cons; [left; cbn; unfold PE_FRAME; clia|]; apply Forall_cons; [left; cbn; unfold PE_FRAME; clia|]; apply Forall_cons; [right; cbn; lia | apply Forall_nil]
| exact ST1 | exact ERR1
| unfold ts0; cbn [t_obj pf_spf pf_mxd]; apply pe_frame_join_ret; [eassumption | exact FRa1 | eassumption | unfold pe_frame_rest; eassumption]
| ].
cbn [pf_spf pf_mxd] in HPRs.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPRs) in TOK; [| eapply client_range_block; [exact INtk | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
clear MU1 WM1 REST LV PB TSK INV.
pose proof INV1 as [_ REST1]. pose proof REST1 as (HP1 & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.
assert (INCL0 : incl LB0 LBall) by (unfold LBall, pe_blocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).

assert (NEWOBJ : forall (entry ra0 : Z) (mc : word -> option byte) (errc : word) (j1c : list byte)
(t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s4' s6' s7' s9' s10' t3' t4' t5' t6' : word),
(entry = json_object_new_int64_entry /\ ra0 = 0x22f50 \/ entry = json_object_new_uint64_entry /\ ra0 = 0x22f64) ->
PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 cb j1c j2 utf sv errc ->
evt rsegs (RZ rsegs md T)
(MS (mkR (Z_to_bv 64 ra0) (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + cop)) s6' s7' (Z_to_bv 64 (sb + co)) s9' s10' (Z_to_bv 64 PE_JTAB) t3' t4' t5' t6')
F (Z_to_bv 64 entry) fc None mc (seg_rom rsegs))).
{ intros until t6'. intros Hent INVc.
pose proof INVc as [_ RESTc]. pose proof RESTc as (HPc & _ & _ & STc & ERRc & _).
apply evt_RZ_done.
assert (KPOST : forall ms2 md2, new_obj_post HIx Sint (Z_to_bv 64 ra0) (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
(Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + cop)) s6' s7' (Z_to_bv 64 (sb + co)) s9' s10' (Z_to_bv 64 PE_JTAB)
F fc mc md LBall lo ms2 md2 -> realizes rsegs (mkCfg ms2 md2) T).
{ intros ms2 md2 (m2 & A2x & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
assert (OUT' : exists A2 NB, HEAP S4L HIx A2 (NB ++ LBall) m2 md2 /\ jres Sint m2 NB r).
{ destruct OUT as [(-> & HP2) | (Hr & BS & J2 & HP2)].
- exists A2x, []. split; [exact HP2 | left; split; reflexivity].
- exists A2x, BS. split; [exact HP2 | right; split; [exact Hr | exact J2]]. }
clear OUT. destruct OUT' as (A2 & NB & HP2 & JR).
pose proof (PE_INVK_call HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INVc HPR2 VM2 HP2 ST2 ERR2) as INVK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
destruct Hent as [[_ Er] | [_ Er]]; rewrite Er; reenter MOK2; step; apply evt_RZ_done;
(eapply (num_tail HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 n ts0 l NB r Sint);
[ exact STC | exact INVK | exact Hl | exact Hst | exact JR | reflexivity | exact Hco | exact Hcb
| tdok TDOK | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM
| unfold mbase; cbn [pf_len t_co pf_mxd]; exact Hn | exact KALL | exact KOUT ]). }
destruct Hent as [[-> ->] | [-> ->]].
- eapply (json_object_new_int64_cps HIx) with (lo := lo); [exact HPc | .. | exact KPOST]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact STc | exact ERRc]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
all: lazymatch goal with |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => vm_compute; reflexivity end.
- eapply (json_object_new_uint64_cps HIx) with (lo := lo); [exact HPc | .. | exact KPOST]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact STc | exact ERRc]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
all: lazymatch goal with |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => vm_compute; reflexivity end. }

step. destruct HRV as [-> | ->].
2:{
if_false. step. rewrite SX0. step. if_true.
apply evt_RZ_done.
eapply (num_err_sw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 ts0 7); [exact STC | exact INV1 | lia | tdok TDOK | exact FS | exact FRM | exact KOUT]. }
if_true.

assert (T14fbc : forall y1 t0' t1' t2' a0v a1v a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
evt rsegs (RZ rsegs md T)
(MS (mkR y1 (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0v a1v a2' a3' a4' a5' a6' a7' (Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 7) (Z_to_bv 64 (sb + cop)) (Z_to_bv 64 pb) s7 (Z_to_bv 64 (sb + co)) s9 s10 (Z_to_bv 64 PE_JTAB) t3' t4' t5' t6')
F (Z_to_bv 64 0x22f08) fc None m1 (seg_rom rsegs))).
{ intros y1 t0' t1' t2' a0v a1v a2' a3' a4' a5' a6' a7' t3' t4' t5' t6'.
pose proof (bv_unsigned_in_range 64 vret) as VR. unfold bv_modulus in VR. cbn in VR.
step. step. if_cases Ks.
-
step. rewrite <- (Z_to_bv_bv_unsigned vret). apply (NEWOBJ json_object_new_uint64_entry 0x22f64 m1 eret (le8 vret ++ le8 wb)); [right; split; reflexivity | exact INV1].
-
pose proof (wmono_refl rsegs m1) as WM2. pose proof (munch_refl [(tk, tk + 72); (spf, spf + 144)] m1) as MU2.
stash INV1.
tk3_walk 0x25784 idtac.
unstash INV1.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m2 _) =>
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md A ts0 cb (le8 vret ++ le8 vret) j2 utf sv eret)
end.
{ eapply (PE_INV_reframe HIx) with (ts := ts0); [exact STC | exact INV1 | exact MU2 | exact WM2 | assumption | | cbn; lia | reflexivity | ].
- unfold ts0, tok_cells, tok_cells_g. cbn [t_pb t_depth ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_mxd]. exact TOK.
- unfold ts0. cbn [t_obj pf_spf pf_mxd]. apply pe_frame_join_ret; [ | | | unfold pe_frame_rest]; eassumption. }
rewrite <- (Z_to_bv_bv_unsigned vret). lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (NEWOBJ json_object_new_int64_entry 0x22f50 mx eret (le8 vret ++ le8 vret)); [left; split; reflexivity | exact INV2] end. }
tk3_walk 0 idtac. if_cases Ke.
- apply T14fbc.
-
pose proof (tok_flags_byte_g mxd fl m1 tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
step. rewrite (zxb_byte fl) by lia. step.
rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia). rewrite (land_mod256 fl 1) by lia.
destruct (land1_cases fl) as [F1 | F1]; rewrite F1.
+ step. if_false. apply T14fbc.
+
step. if_true. apply evt_RZ_done.
eapply (num_err_sw HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 ts0 7);
[exact STC | exact INV1 | lia | tdok TDOK | exact FS | exact FRM | exact KOUT].
Qed.
End PeNumUint.

End RC__1.
End Mq1.

From Stdlib Require Import ZArith List Lia Bool.
From Stdlib Require Import Sorting.Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UEQM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UEQM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.ZBridge. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QWxq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qc3B.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qc3B.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfYR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfYR. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfcC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfcC.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q7wb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7wb.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QHnV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHnV. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QCcH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCcH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QfLs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QfLs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q0Ek.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q0Ek. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qtgi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qtgi. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QjDH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QjDH.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UC8c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UC8c.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Qsw7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qsw7. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRUw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq2.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UtMn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UtMn.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uy2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uy2A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdFq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdFq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85.
Import ListNotations. Unset Keyed Unification. Local Ltac Stdlib.micromega.Lia.lia ::= QsRG.Mq0.mkr__lia_0. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Stdlib.micromega.Lia.nia ::= QsRG.Mq0.mkr__nia_1. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3 Require Tk3Tac. Import TopUbTac Tk1Tac Tk3Tac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Lemma map_unsigned_bytes : forall bs : list byte, map (Z_to_bv 8) (map bv_unsigned bs) = bs.
Proof. induction bs as [|b bs IH]; [reflexivity|]. cbn. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

#[using="Type"] Lemma numb_forall_numch : forall bs, Forall (fun b => numb b = true) bs -> Forall (fun c => is_numch c = true) (map bv_unsigned bs).
Proof. induction bs as [|b bs IH]; intros H; [constructor|]. apply Forall_cons_iff in H as [H1 H2]. cbn. constructor; [exact H1 | apply IH; exact H2]. Qed.

#[using="Type"] Lemma numb_forall_nox : forall bs, Forall (fun b => numb b = true) bs -> Forall (fun c => c <> 120 /\ c <> 88) (map bv_unsigned bs).
Proof.
induction bs as [|b bs IH]; intros H; [constructor|]. apply Forall_cons_iff in H as [H1 H2]. cbn. constructor; [| apply IH; exact H2].
unfold numb, numch in H1. split; intros E; rewrite E in H1; cbn in H1; discriminate.
Qed.

#[using="Type"] Lemma forall_range_unsigned : forall bs : list byte, Forall (fun c => 0 <= c < 256) (map bv_unsigned bs).
Proof. induction bs as [|b bs IH]; [constructor|]. cbn. constructor; [| exact IH]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. Qed.

#[using="Type"] Lemma numb_not_in_b0 : forall bs, Forall (fun b => numb b = true) bs -> ~ In b0 bs.
Proof.
intros bs H Hin. apply Forall_forall with (x := b0) in H; [| exact Hin]. unfold numb, numch in H. change (bv_unsigned b0) with 0 in H. cbn in H. discriminate.
Qed.

#[using="Type"] Lemma fsaved_of_strtod : forall F F' : bvmap 5 word,
(forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> Sem.reg_get F' k = Sem.reg_get F k) ->
fsaved F F'.
Proof.
intros F F' H k Hk. unfold FSAVED in Hk. cbn in Hk.
apply H; (destruct Hk as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]; vm_compute; discriminate).
Qed.

Section PeNumDbl.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis STRTOD : rstrtod_stmt.
Hypothesis STRDUP : strdup_stmt HIx.

Let LB0 : list blk := LB0 pf LBc.

#[using="STRTOD"] Lemma strtod_specZ :
forall (ra gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
(SP TA PE : Z) (pre : list byte) (bits used : Z) (ejunk : word) (lw : Z) (canary ev : word),
bytes_at rsegs m TA (pre ++ [b0]) -> Forall (fun b => numb b = true) pre ->
Z.of_nat (length pre) < 2^30 ->
rw_cells rsegs m PE [C8 ejunk] ->
scan_strtod (map bv_unsigned pre ++ [0]) = Some (bits, used) ->
stk rsegs m lw SP -> lw <= SP - RSTRTOD_DEPTH -> RGLOBALS_TOP <= lw -> 0 <= SP < 2^62 ->
0 < TA -> (TA + Z.of_nat (length pre) + 1 <= RIMG_LO \/ RGLOBALS_TOP <= TA) -> TA + Z.of_nat (length pre) + 1 <= lw ->
SP <= PE -> PE + 8 <= 2^63 ->
ssp_cells m canary -> rw_cells rsegs m RERRNO [C4 ev] ->
mem_inv rsegs m -> frm0 fc ->
evt rsegs (rstrtod_post ra (Z_to_bv 64 SP) gp (Z_to_bv 64 RATP) s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F TA PE (map bv_unsigned pre ++ [0]) (Z.of_nat (length pre)) bits used lw canary m)
(MS (mkR ra (Z_to_bv 64 SP) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 TA) (Z_to_bv 64 PE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 RSTRTOD) fc None m (seg_rom rsegs)).
Proof.
intros until ev. intros TXT NUM LPRE EP SCAN ST LOS GT SPR TPOS TLO THI SPE PEHI SSP ERR MI FRM.
pose proof STRTOD as SD. unfold rstrtod_stmt in SD.
assert (ZL : zlength (map bv_unsigned pre) = Z.of_nat (length pre)) by (unfold zlength; rewrite length_map; reflexivity).
specialize (SD ra (Z_to_bv 64 SP) gp (Z_to_bv 64 RATP) t0 t1 t2 s0 s1 (Z_to_bv 64 TA) (Z_to_bv 64 PE) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
F fc m TA PE (map bv_unsigned pre ++ [0]) (map bv_unsigned pre) [] bits used ejunk lw canary ev).
rewrite ZL in SD. rewrite !(unsigned_lit SP) in SD by lia.
apply SD; clear SD.
- rewrite map_app. cbn [map pf_mxd]. rewrite map_unsigned_bytes. exact TXT.
- apply Forall_app. split; [apply forall_range_unsigned | constructor; [lia | constructor]].
- reflexivity.
- apply numb_forall_numch. exact NUM.
- lia.
- unfold zlength. rewrite length_app, length_map. cbn [length pf_mxd]. lia.
- exact EP.
- exact SCAN.
- exact ST.
- lia.
- exact GT.
- lia.
- exact TPOS.
- left. unfold zlength. rewrite length_app, length_map. cbn [length pf_mxd]. split; [unfold RIMG_LO, RGLOBALS_TOP in *; lia | lia].
- unfold RGLOBALS_TOP, RIMG_LO, RSTRTOD_DEPTH in *. lia.
- exact SPE.
- exact PEHI.
- right. unfold zlength. rewrite length_app, length_map. cbn [length pf_mxd]. unfold RSTRTOD_DEPTH in *. lia.
- exact SSP.
- exact ERR.
- exact MI.
- exact FRM.
- reflexivity.
- reflexivity.
- reflexivity.
Qed.

#[using="STRTOD STRDUP"] Lemma num_double :
forall (n : nat) (ts : tstate) (l : tlevel) (txt : list byte)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word) (cop : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s7 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
pbufc rsegs m (t_pbs ts) (t_pb ts) txt -> Forall (fun b => numb b = true) txt -> Z.of_nat (length txt) <= pf_len pf ->
bytes_at rsegs me GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
(mbase pf ts + 8 <= n)%nat ->
KALL HIx pf q LBc payload me lo sv T F0 n -> KOUT7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x22d30 cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
s4 (Z_to_bv 64 (t_pb ts)) s7 (Z_to_bv 64 (pf_sb pf + t_co ts)) s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst PBC NUM LTXT GOTU Hco Hcb TDOK FS FRM Hn KALL KOUT.
pose proof KALL as [KLOOP [KREDO [KBRK KBRK2]]].
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK.
unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold mbase in Hn. cbn [pf_len t_co pf_mxd] in Hn. unfold PE_FRAME in SP0.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (LBall := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) in *.
assert (INtk : In (tk, 72) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.

pose proof PBC as (buf & bpos & cap & post & Epbs & Ltxt & PCORE). pose proof PCORE as (Hbpos & Hcap & Hclen & PBS & PBUF). cbn [hl_segs S4L pf_mxd] in PBS, PBUF.
assert (INpb : In (pb, 16) LBall) by (unfold LBall, pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
assert (INbuf : In (buf, cap) LBall) by (unfold LBall, pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ pb 16 HP INpb) as Himg_pb. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_pb.
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & Hbufal & Hbuflo & Hbufhi & _).
pose proof (heap_blk_img S4L HIx _ _ _ _ buf cap HP INbuf) as Himg_buf. cbn [hl_img_lo hl_img_hi S4L pf_mxd] in Himg_buf.
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi, Hbufhi.
rewrite !length_app in Hclen. cbn [length pf_mxd] in Hclen.
assert (TXT0 : bytes_at rsegs m buf (txt ++ [b0])).
{ pose proof (rw_cells_bytes_at' _ _ _ _ PBUF) as X. cbn [cells_bytes cbytes pf_mxd] in X. rewrite app_nil_r in X.
rewrite app_assoc in X. apply bytes_at_app in X. exact (proj1 X). }

pose proof (heap_canary S4L HIx _ _ _ _ HP) as (g & CAN1 & CAN2 & _). cbn [hl_got_guard hl_guard hl_segs S4L pf_mxd] in CAN1, CAN2.
pose proof (pe_frame_split3 _ _ _ _ _ _ _ _ FR) as (FRlo & (w0 & Ew0 & FE) & FRhi). unfold pe_frame_lo in FRlo. unfold pe_frame_hi in FRhi.
destruct (scan_strtod_total_gen (map bv_unsigned txt) (forall_range_unsigned txt) (numb_forall_nox txt NUM)) as (bits & used & SCAN & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
change (0x77c00 - 164) with 490332 in ERR.

assert (GOT0 : bytes_at rsegs m GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F)))).
{ eapply (heap_presx_bytes_at S4L); [exact HPR | exact GOTU |]. right; left. intros a Ha. rewrite length_le8 in Ha. unfold GOT_free_userdata in Ha. cbn. unfold s4_client_static, s4_volatile. lia. }
assert (INCL0 : incl LB0 LBall) by (unfold LBall, pe_blocks; intros b Hb; apply in_or_app; right; right; right; exact Hb).
apply (PE_REST_base HIx) in REST as (BASE & LVx & OBJx).
assert (USPF : bv_unsigned (Z_to_bv 64 spf) = spf) by (apply unsigned_lit; lia).
stash PB. stash TSK. stash BASE. stash LV. stash TOK. stash GOT0. clear LVx OBJx HPR PBUF.
pose proof (munch_refl [(lo, spf); (spf + 32, spf + 40); (490332, 490336)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
apply rz_evt; [exact MOK|].
tk3_walk 0x5b4fc ltac:(try (norm_sx32; rewrite <- Ltxt)).

lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [ eapply (strtod_specZ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm spf buf (spf + 32) txt bits used w0 lo g errv)
| unfold rstrtod_post, RERRNO; post_call segs mm ] end.
1:{ exact TXT0. } 1:{ exact NUM. } 1:{ lia. } 1:{ exact FE. } 1:{ exact SCAN. } 1:{ exact ST. }
1:{ unfold RSTRTOD_DEPTH. lia. } 1:{ unfold RGLOBALS_TOP. lia. } 1:{ lia. } 1:{ lia. } 1:{ unfold RIMG_LO, RGLOBALS_TOP. lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. }
1:{ apply ssp_cells_of_canary; [exact CAN1 | exact CAN2]. } 1:{ exact ERR. } 1:{ exact MI. } 1:{ exact FRM. }
cbv beta. unfold RERRNO in *.

match goal with H : Qc3B.frm0 ?f |- _ => rename H into FRM1; change (Qc3B.frm0 f) with (frm0 f) in FRM1 end.
match goal with H : forall k : bv 5, _ -> _ -> _ -> Sem.reg_get ?F1 k = Sem.reg_get F k |- _ => rename H into REGF; pose proof (fsaved_of_strtod F F1 REGF) as FS1 end.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end. rename MU into MU1. rename WM into WM1.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
match goal with H : stk rsegs m1 lo _ |- _ => rename H into ST1; rewrite ?USPF in ST1 end.
match goal with H : rw_cells rsegs m1 (spf + 32) [C8 (Z_to_bv 64 (buf + ?u))] |- _ => rename H into FE1 end.
match goal with H : rw_cells rsegs m1 490332 [C4 ?e] |- _ => rename H into ERR1 end.

unstash PB. unstash TSK. unstash BASE. unstash LV. unstash TOK. unstash GOT0.
assert (HPRs : heap_pres S4L LBall (spf + 144) m m1).
{ eapply (heap_pres_of_munch S4L); [exact MU1 | exact WM1 |].
eapply (client_outside S4L HIx); [exact HP | intros b Hb; exact Hb | clia |].
apply Forall_cons; [left; cbn; clia|]. apply Forall_cons; [left; cbn; clia|]. apply Forall_cons; [right; right; cbn; intros; lia | apply Forall_nil]. }
assert (AG1 : agree_on rsegs LBall m m1) by (eapply (agree_of_heap_pres rsegs S4L); [exact HPRs | reflexivity | intros b Hb; exact Hb]).
match type of ERR1 with rw_cells _ _ _ [C4 ?e] =>
assert (BASE1 : PE_BASE HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) LB0 payload me lo m1 md A LBall e)
by (eapply (PE_BASE_stackcall HIx); [exact STC | exact BASE | exact INCL0 | exact MU1 | exact WM1 | exact MI1 | | exact ST1 | exact ERR1];
apply Forall_cons; [left; cbn; unfold PE_FRAME; clia|]; apply Forall_cons; [left; cbn; unfold PE_FRAME; clia|]; apply Forall_cons; [right; cbn; lia | apply Forall_nil])
end.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPRs) in TOK; [| eapply client_range_block; [exact INtk | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
pose proof PCORE as (_ & _ & _ & _ & PBUF). cbn [hl_segs S4L pf_mxd] in PBUF.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPRs) in PBUF; [| eapply client_range_block; [exact INbuf | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in PBUF.
apply (tstack_pres_g S4L _ _ _ _ _ _ HPRs INq) in TSK; [| exact LEN32]. cbn [hl_segs S4L pf_mxd] in TSK.
apply (heap_pres_bytes_at S4L _ _ _ _ _ _ HPRs) in GOT0; [| right; left; intros a Ha; rewrite length_le8 in Ha; unfold GOT_free_userdata in Ha; cbn; unfold s4_client_static; lia]. cbn [hl_segs S4L pf_mxd] in GOT0.
assert (PB1 : pbuf rsegs m1 pbs pb) by (eapply pbuf_agree; [exact PB | exact AG1 | intros b Hb; unfold LBall, pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; apply in_or_app; left; apply in_or_app; left; exact Hb]).
assert (LV1 : forall i li, nth_error levels i = Some li -> lvl_cur rsegs S4F m1 depth i li).
{ intros i li Hli. eapply (lvl_cur_agree rsegs S4F); [exact (LV i li Hli) | exact AG1 |].
intros b Hb. unfold LBall, pe_blocks, tstate_blocks, ts0. apply in_or_app; left. apply in_or_app; right. apply in_or_app; right.
apply in_concat. exists (lvl_blocks li). split; [| exact Hb]. apply in_map. eapply nth_error_In. exact Hli. }
assert (Eobjbs : objbs = []).
{ revert OBJ. unfold cur_st, ts0. cbn [t_levels t_depth t_objbs pf_mxd]. rewrite Hl, Hst. cbn. intros E; exact E. }
match goal with |- evt _ _ (MS _ ?F1 _ _ _ _ _) =>
match type of ERR1 with rw_cells _ _ _ [C4 ?e] =>
assert (INV1 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m1 md A ts0 cb j1 j2 (le8 (Z_to_bv 64 (buf + used))) sv e)
end end.
{ split.
- unfold PE_CORE, ts0. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff pf_len pf_tk pf_spf pf_mxd].
split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOK|].
split; [exact PB1|]. split; [exact Hpb|]. split; [exact TSK|].
apply pe_frame_join3; [unfold pe_frame_lo; assumption | exact FE1 | unfold pe_frame_hi; assumption].
- apply (PE_REST_of_base HIx); [exact BASE1 | exact LV1 |].
unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite Hl, Hst. cbn. exact Eobjbs. }
clear BASE LV PB MU1 WM1.
pose proof (proj1 BASE1) as HP1.
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.

tk3_walk 0 idtac.
destruct (Z.eq_dec used (Z.of_nat (length txt))) as [UEQ | UNE].
2:{
first [if_truex | if_falsex].
pose proof (wmono_refl rsegs m1) as WM2. pose proof (munch_refl [(tk, tk + 72); (spf, spf + PE_FRAME)] m1) as MU2.
stash INV1. stash BASE1.
tk3_walk 0x23ea8 idtac.
unstash INV1. unstash BASE1.
apply evt_RZ_done.
replace (Z_to_bv 64 buf) with (Z_to_bv 64 (sb + (buf - sb))) by (f_equal; lia). eapply (KOUT (TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) (Z_to_bv 64 7) ucs high quote) obj objs objbs) []).
2:{ tdok TDOK. } 2:{ eapply fsaved_trans; [exact FS | exact FS1]. } 2:{ exact FRM1. }
apply (PE_INV_W HIx).
eapply (PE_INV_retok HIx) with (ts := ts0); [exact STC | exact INV1 | exact MU2 | exact WM2 | assumption | | cbn; lia | reflexivity | ].
+ unfold ts0, tok_cells, tok_cells_g. cbn [t_pb t_depth ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_tk pf_mxd]. assumption.
+ unfold ts0. cbn [t_obj pf_spf pf_mxd]. apply pe_frame_join3; [unfold pe_frame_lo; eassumption | eassumption | unfold pe_frame_hi; eassumption]. }
first [if_truex | if_falsex].
tk3_walk 0x26058 idtac.

assert (SIB : str_in_block S4L m1 buf cap (txt ++ [b0] ++ post) buf txt).
{ split; [exact PBUF|]. split; [lia|]. split; [lia|]. split; [| apply numb_not_in_b0; exact NUM].
rewrite Z.sub_diag. change (skipn (Z.to_nat 0) (txt ++ [b0] ++ post)) with (txt ++ [b0] ++ post).
rewrite app_assoc, firstn_app, firstn_all2 by (rewrite length_app; cbn; lia).
rewrite length_app. cbn [length pf_mxd]. replace (length txt + 1 - (length txt + 1))%nat with 0%nat by lia. cbn. rewrite app_nil_r. reflexivity. }
pose proof (proj1 (proj2 BASE1)) as ST1'. pose proof (proj1 (proj2 (proj2 BASE1))) as ERR1'.
stash INV1. stash BASE1.
apply evt_RZ_done.
eapply (json_object_new_double_s_cps HIx STRDUP) with (LB := LBall) (lo := lo) (ds := buf) (b := buf) (n := cap) (str := txt) (bytes := txt ++ [b0] ++ post);
[ exact HP1 | exact INbuf | exact SIB | lia | exact GOT0 | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST1' | exact ERR1']).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (m2 & A2x & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & TXT2 & OUT).
destruct RS2 as (w0' & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
unstash INV1. unstash BASE1.
assert (OUT' : exists A2 NB, HEAP S4L HIx A2 (NB ++ LBall) m2 md2 /\ jres (Sdouble true) m2 NB r).
{ destruct OUT as [(-> & HP2) | (Hr & BS & J2 & HP2)].
- exists A2x, []. split; [exact HP2 | left; split; reflexivity].
- exists A2x, BS. split; [exact HP2 | right; split; [exact Hr | exact J2]]. }
clear OUT. destruct OUT' as (A2 & NB & HP2 & JR).
pose proof (PE_INVK_call HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INV1 HPR2 VM2 HP2 ST2 ERR2) as INVK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
lazymatch goal with |- context [ret_pc (Z_to_bv 64 ?a)] =>
replace (ret_pc (Z_to_bv 64 a)) with (Z_to_bv 64 a) by (symmetry; apply ret_pc_even; [ lia | reflexivity ]) end.
replace (Z_to_bv 64 buf) with (Z_to_bv 64 (sb + (buf - sb))) by (f_equal; lia). eapply (num_tail HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 n ts0 l NB r (Sdouble true));
[ exact STC | exact INVK | exact Hl | exact Hst | exact JR | reflexivity | exact Hco | exact Hcb
| tdok TDOK | eapply fsaved_trans; [exact FS | eapply fsaved_trans; [exact FS1 | exact FS2]]
| apply FRM2; exact FRM1
| unfold mbase; cbn [pf_len t_co pf_mxd]; exact Hn | exact KALL | exact KOUT ].
Qed.
End PeNumDbl.

End RC__1.
