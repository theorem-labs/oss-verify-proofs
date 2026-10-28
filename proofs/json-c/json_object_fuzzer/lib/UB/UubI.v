(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)


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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QRjH.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRjH.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QRUw.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT8C.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT8C. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UV3d.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UV3d.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QkMG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QkMG.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UG8z.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UG8z. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U2Sr.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U2Sr. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require ULbz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import ULbz. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UIsM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UIsM.Mq2. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UXfU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4Eu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4Eu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc8V.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdFq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdFq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UvXs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UvXs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYrb.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYrb.Mq1.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3 Require Tk3Tac. Import TopUbTac Tk1Tac Tk3Tac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Section PeNumInt.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis STRTOLL : strtox_stmt strtoll_entry.
Hypothesis STRTOULL : strtox_stmt strtoull_entry.
Let LB0 : list blk := LB0 pf LBc.

#[using="STRTOLL STRTOULL"] Lemma num_int :
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
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x22e4c cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
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
pose proof Hn as Hn0. unfold mbase in Hn. cbn [pf_len t_co pf_mxd] in Hn.
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
2:{
first [if_truex | if_falsex]. tk3_walk 0x22e88 idtac.
unstash PB. unstash TSK. unstash REST. unstash LV.
apply evt_RZ_done.
eapply (num_uint HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOULL n ts0 l txt);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | exact NUM | exact LTXT | exact SX0 | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT]. }
first [if_truex | if_falsex]. tk3_walk 0x28f94 idtac.

pose proof (munch_refl [(spf - 416, spf); (spf + 16, spf + 16 + 8); (490332, 490336)] m) as MU. pose proof (wmono_refl rsegs m) as WM.
stash TOK.
pose proof (json_parse_int64_spec STRTOLL) as PU. unfold parse_i64_stmt in PU.
lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
eapply evt_cut; [ eapply PU with (SP := spf) (A := buf) (R := spf + 16) (lo := lo) (str := txt)
| unfold parse_i64_post, parse_i64_W; post_call segs mm ] end.
all: clear PU.
1:{ exact USPF. } 1:{ reflexivity. } 1:{ reflexivity. } 1:{ exact TXT0. } 1:{ apply numb_not_in_b0'; exact NUM. } 1:{ lia. } 1:{ lia. }
1:{ exact FRb. } 1:{ lia. } 1:{ lia. } 1:{ clear - SPA. Z.div_mod_to_equations; lia. } 1:{ exact ERR. } 1:{ reflexivity. } 1:{ exact CAN1. } 1:{ exact CAN2. } 1:{ exact ST. }
1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ vm_compute; reflexivity. } 1:{ exact MI. }
cbv beta. change (0x77c00 - 164) with 490332 in *.
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end. rename MU into MU1. rename WM into WM1.
match goal with H : mem_inv rsegs m1 |- _ => rename H into MI1 end.
match goal with H : stk rsegs m1 lo _ |- _ => rename H into ST1 end.
match goal with H : rw_cells rsegs m1 (spf + 16) [C8 ?v] |- _ => rename H into FRb1 end.
match goal with H : rw_cells rsegs m1 490332 [C4 ?e] |- _ => rename H into ERR1 end.
match goal with H : ?rv = 0 \/ ?rv = 1 |- _ => rename H into HRV end.
lazymatch type of FRb1 with rw_cells _ _ _ [C8 ?vv] => rename vv into vret end.
lazymatch type of ERR1 with rw_cells _ _ _ [C4 ?ee] => rename ee into eret end.
unstash TOK. unstash PB. unstash TSK. unstash REST. unstash LV.
destruct (PE_INV_stackcall HIx _ _ _ _ _ _ m m1 _ _ ts0 cb cb j1 (le8 wa ++ le8 vret) j2 utf utf sv errv eret _ STC INV MU1 WM1 MI1) as [INV1 HPRs];
[ apply Forall_cons; [left; cbn; unfold PE_FRAME; clia|]; apply Forall_cons; [left; cbn; unfold PE_FRAME; clia|]; apply Forall_cons; [right; cbn; lia | apply Forall_nil]
| exact ST1 | exact ERR1
| unfold ts0; cbn [t_obj pf_spf pf_mxd]; apply pe_frame_join_ret; [eassumption | eassumption | exact FRb1 | unfold pe_frame_rest; eassumption]
| ].
cbn [pf_spf pf_mxd] in HPRs.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPRs) in TOK; [| eapply client_range_block; [exact INtk | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
assert (PBC1 : pbufc rsegs m1 pbs pb txt).
{ eapply pbufc_pres; [exact PBC | exact HPRs |]. intros b Hb. unfold LBall, pe_blocks, tstate_blocks, ts0. cbn [t_pbs pf_mxd]. apply in_or_app; left. apply in_or_app; left. exact Hb. }
clear MU1 WM1 REST LV PB TSK INV.
pose proof INV1 as [_ REST1]. pose proof REST1 as (HP1 & _ & _ & ST1' & ERR1' & _).
pose proof (heap_model_ok _ _ _ _ _ _ HP1) as MOK1.

step. destruct HRV as [-> | ->].
2:{
if_false. tk3_walk 0x22e88 ltac:(try rewrite SX0).
apply evt_RZ_done.
eapply (num_uint HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOULL n ts0 l txt);
[exact STC | exact INV1 | exact Hl | exact Hst | exact PBC1 | exact NUM | exact LTXT | exact SX0 | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT]. }
if_true.

assert (T14fec : forall y1 t0' t1' t2' a0v a1v a2' a3' a4' a5' a6' a7' s4' s6' s7' s9' s10' t3' t4' t5' t6',
evt rsegs (RZ rsegs md T)
(MS (mkR y1 (Z_to_bv 64 spf) gp (Z_to_bv 64 490496) t0' t1' t2' (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
a0v a1v a2' a3' a4' a5' a6' a7' (Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4' (Z_to_bv 64 (sb + cop)) s6' s7' (Z_to_bv 64 (sb + co)) s9' s10' (Z_to_bv 64 PE_JTAB) t3' t4' t5' t6')
F (Z_to_bv 64 0x22f48) fc None m1 (seg_rom rsegs))).
{ intros y1 t0' t1' t2' a0v a1v a2' a3' a4' a5' a6' a7' s4' s6' s7' s9' s10' t3' t4' t5' t6'.
step. step.

apply evt_RZ_done.
eapply (json_object_new_int64_cps HIx) with (lo := lo); [exact HP1 | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST1' | exact ERR1']).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
all: try lazymatch goal with |- bv_unsigned (Z_to_bv 64 _) mod 2 = 0 => vm_compute; reflexivity end.
intros ms2 md2 (m2 & A2x & r & errv2 & RS2 & VM2 & ST2 & HPR2 & ERR2 & OUT).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
assert (OUT' : exists A2 NB, HEAP S4L HIx A2 (NB ++ LBall) m2 md2 /\ jres Sint m2 NB r).
{ destruct OUT as [(-> & HP2) | (Hr & BS & J2 & HP2)].
- exists A2x, []. split; [exact HP2 | left; split; reflexivity].
- exists A2x, BS. split; [exact HP2 | right; split; [exact Hr | exact J2]]. }
clear OUT. destruct OUT' as (A2 & NB & HP2 & JR).
pose proof (PE_INVK_call HIx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ STC INV1 HPR2 VM2 HP2 ST2 ERR2) as INVK.
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
reenter MOK2. step. apply evt_RZ_done.
eapply (num_tail HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 n ts0 l NB r Sint);
[ exact STC | exact INVK | exact Hl | exact Hst | exact JR | reflexivity | exact Hco | exact Hcb
| tdok TDOK | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM
| exact Hn0 | exact KALL | exact KOUT ]. }
tk3_walk 0 idtac. if_cases Ke.
- apply T14fec.
-
pose proof (tok_flags_byte_g mxd fl m1 tk pb (Z.of_nat depth) q (TS isd stpos (Z_to_bv 64 co) err ucs high quote) TOK) as RDF.
step. rewrite (zxb_byte fl) by lia. step.
rewrite (unsigned_lit (fl mod 256)) by (pose proof (Z.mod_pos_bound fl 256 ltac:(lia)); lia). rewrite (land_mod256 fl 1) by lia.
destruct (land1_cases fl) as [F1 | F1]; rewrite F1.
+ step. if_false. apply T14fec.
+
step. if_true. step. apply evt_RZ_done.
eapply (num_err_sw28 HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 ts0 7);
[exact STC | exact INV1 | lia | tdok TDOK | exact FS | exact FRM | exact KOUT].
Qed.
End PeNumInt.

End RC__1.
