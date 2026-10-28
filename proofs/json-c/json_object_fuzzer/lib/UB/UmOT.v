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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Lib.GwApply.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.Lib.GwApply.Bytes.
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
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UXfU.Mq0. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Udyh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Udyh.Mq7.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QJjn.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QJjn.Mq0.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UBpZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UBpZ. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UT7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UT7i. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uv6q.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uv6q.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require QgoP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QgoP.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UzWc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UzWc.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require U4Eu.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import U4Eu.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uc8V.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uc8V.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UfOM.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UfOM.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require Uy2A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Uy2A. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UdFq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UdFq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UvXs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UvXs. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UX85.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UX85.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYrb.Mq1. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UubI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UubI. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UYrb.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UYrb. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UbRq.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UbRq. From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB Require UTq4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import UTq4.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Top Require TopUbTac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk1 Require Tk1Tac.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib.UB.Tk3 Require Tk3Tac.
Import ListNotations. Unset Keyed Unification. Local Ltac Qfw3.Mq3.model_reg_tac n X mexpr ::= Qfw3.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3.Mq3.zeq_fast ::= Qfw3.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import TopUbTac Tk1Tac Tk3Tac.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

Definition pe_jtab_num := Eval vm_compute in match image_bytes rsegs 0x1352c 260 with Some bs => bs | None => [] end.
#[using="Type"] Lemma pe_jtab_num_ro : forall m, mem_inv rsegs m -> ro_cells rsegs m 0x1352c [CB 260 pe_jtab_num].
Proof.
intros m MI. change 260%nat with (length pe_jtab_num).
apply ro_cells_image; [exact MI | vm_compute; reflexivity | lia | ].
change (Z.of_nat (length pe_jtab_num)) with 260%Z. lia.
Qed.
#[using="Type"] Lemma ro_cells_bytes_at'' : forall segs m A cs, ro_cells segs m A cs -> bytes_at segs m A (cells_bytes cs).
Proof. intros segs m A cs [_ H]. exact H. Qed.

Definition numfollow (c : Z) : bool :=
(c =? 9) || (c =? 10) || (c =? 13) || (c =? 32) || (c =? 44) || (c =? 47) || (c =? 73) || (c =? 93) || (c =? 105) || (c =? 125).
Definition pe_jt_num (c : Z) : Z := if numfollow c then 0x229f4 else 0x23e18.
End RC__1.

Lemma enum_step_Z : forall v lo lo' : Z, lo' = (lo + 1)%Z -> (lo <= v)%Z -> v = lo \/ (lo' <= v)%Z.
Proof. intros v lo lo' -> H. destruct (Z.eq_dec v lo) as [E|N]; [left; exact E | right; lia]. Qed.
Ltac enum_from_go v lo n L :=
lazymatch n with
| O => exfalso; lia
| S ?n' => let E := fresh "E" in let L2 := fresh "EL" in
let lo' := eval vm_compute in (lo + 1)%Z in
destruct (enum_step_Z v lo lo' eq_refl L) as [E | L2]; clear L;
[ rewrite ?E in * | enum_from_go v lo' n' L2 ]
end.
Ltac enum_from v lo n :=
let L := fresh "EL" in assert (L : (lo <= v)%Z) by lia; enum_from_go v lo n L.
Section RC__2. Context {RC__ : Q6q3.RunConsts}.

Section PeNumPost.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis STRTOLL : strtox_stmt strtoll_entry.
Hypothesis STRTOULL : strtox_stmt strtoull_entry.
Hypothesis STRTOD : rstrtod_stmt.
Hypothesis STRDUP : strdup_stmt HIx.
Let LB0 : list blk := LB0 pf LBc.

#[using="STRTOLL STRTOULL STRTOD STRDUP"] Lemma num_infchk :
forall (n : nat) (ts : tstate) (l : tlevel) (txt : list byte)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word) (cop : Z)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
pbufc rsegs m (t_pbs ts) (t_pb ts) txt -> Forall (fun b => numb b = true) txt -> Z.of_nat (length txt) <= pf_len pf ->
bytes_at rsegs me GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
(mbase pf ts + 8 <= n)%nat ->
KALL HIx pf q LBc payload me lo sv T F0 n -> KOUT7 HIx pf q LBc payload me lo sv T F0 -> KERR7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x22a14 cop x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
s4 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (Z.of_nat (length txt))) (Z_to_bv 64 (pf_sb pf + t_co ts)) s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst PBC NUM LTXT GOTU Hco Hcb TDOK FS FRM Hn KALL KOUT KERR.
pose proof KALL as [_ [KREDO _]].
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & _).
destruct ts as [depth levels co pb pbs x obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct x as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR.
unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
pose proof Hn as Hn0. unfold mbase in Hn. cbn [pf_len t_co pf_mxd] in Hn.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (LBall := pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0) in *.
assert (INtk : In (tk, 72) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; left; reflexivity).
assert (INq : In (q, (32 * mxd)) LBall) by (unfold LBall, pe_blocks; apply in_or_app; right; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ tk 72 HP INtk) as (_ & Htal & Htlo & Hthi & _).
pose proof (heap_blk S4L HIx _ _ _ _ q (32 * mxd) HP INq) as (_ & Hqal & Hqlo & Hqhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hthi, Hqhi.
pose proof PBC as (buf & bpos & cap & post & Epbs & Ltxt & PCORE). pose proof PCORE as (Hbpos & Hcap & Hclen & PBS & PBUF). cbn [hl_segs S4L pf_mxd] in PBS, PBUF.
assert (INbuf : In (buf, cap) LBall) by (unfold LBall, pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; right; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ buf cap HP INbuf) as (_ & Hbufal & Hbuflo & Hbufhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hbufhi.
assert (INpb : In (pb, 16) LBall) by (unfold LBall, pe_blocks, tstate_blocks, ts0; cbn [t_pbs pf_mxd]; rewrite Epbs; apply in_or_app; left; apply in_or_app; left; left; reflexivity).
pose proof (heap_blk S4L HIx _ _ _ _ pb 16 HP INpb) as (_ & Hpbal & Hpblo & Hpbhi & _).
unfold alloc_ceiling, sp_window_lo, stack_max_size in Hpbhi.
pose proof (pe_pbs_sep HIx _ _ _ ts0 _ _ _ _ pb buf cap STC HP Epbs) as (Dpbbuf & Dtkpb & Dtkbuf & Dqpb & Dqbuf). cbn [pf_tk pf_mxd] in Dtkpb, Dtkbuf, Dqpb, Dqbuf.
assert (Htq : tk <> q).
{ pose proof (heap_blk_nodup S4L HIx _ _ _ _ HP) as ND. unfold LBall, pe_blocks in ND. rewrite map_app in ND. apply NoDup_app_remove_l in ND.
cbn [map blk_addr fst pf_mxd] in ND. apply List.NoDup_cons_iff in ND as [Hni _]. intros E. apply Hni. left. symmetry. exact E. }
pose proof (heap_blk_disjoint S4L HIx _ _ _ _ tk 72 q (32 * mxd) HP INtk INq Htq) as Hdtq.
rewrite !length_app in Hclen. cbn [length pf_mxd] in Hclen.
assert (TXT0 : bytes_at rsegs m buf (txt ++ [b0])).
{ pose proof (rw_cells_bytes_at' _ _ _ _ PBUF) as X. cbn [cells_bytes cbytes pf_mxd] in X. rewrite app_nil_r in X.
rewrite app_assoc in X. apply bytes_at_app in X. exact (proj1 X). }
destruct (nth_error (txt ++ [b0]) 0) as [c0|] eqn:Hc0; [| apply nth_error_None in Hc0; rewrite length_app in Hc0; cbn in Hc0; lia].
pose proof (string_byte m buf _ 0 c0 TXT0 Hc0 ltac:(lia)) as RD0. rewrite Z.add_0_r in RD0.
pose proof (bv_unsigned_in_range 8 c0) as C0R. unfold bv_modulus in C0R. cbn in C0R.
pose proof (bv_unsigned_in_range 8 cb) as CBR. unfold bv_modulus in CBR. cbn in CBR.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.

pose proof (LV depth l Hl) as LVd. pose proof LVd as (ST26 & SS26 & _ & Md).
rewrite Nat.ltb_irrefl, Nat.eqb_refl in Md. destruct Md as (cc0 & hn0 & Hmode & CLS0 & NM0).
rewrite Hst in Hmode. pose proof (number_mode _ _ _ SS26 Hmode) as [Ecc Ehn]. subst cc0 hn0.
assert (Ess : tl_ss l = ST_start).
{ clear - SS26 Hmode. enum_z SS26 (tl_ss l); vm_compute in Hmode; first [discriminate Hmode | reflexivity]. }
pose proof (TSK depth l Hl) as Ld. unfold srec_cells in Ld.
remember (q + 32 * Z.of_nat depth) as bse eqn:Hbse in Ld.
assert (HbseR : q <= bse /\ bse + 32 <= q + (32 * mxd)) by (subst bse; lia).

assert (TO_TRIM : forall r0 r3 r4 r5 r6 r7 u0 u1 u2 u3 u4 u5 u6,
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) u0 u1 u2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
r0 (Z_to_bv 64 buf) (Z_to_bv 64 (bv_unsigned c0)) r3 r4 r5 r6 r7 (Z_to_bv 64 newl) (Z_to_bv 64 lenr) s4 (Z_to_bv 64 (sb + cop)) (Z_to_bv 64 pb) (Z_to_bv 64 (Z.of_nat (length txt))) (Z_to_bv 64 (sb + co)) s9 s10 (Z_to_bv 64 PE_JTAB) u3 u4 u5 u6)
F (Z_to_bv 64 0x22ab8) fc None m (seg_rom rsegs))).
{ intros r0 r3 r4 r5 r6 r7 u0 u1 u2 u3 u4 u5 u6.
step. replace (zx32 (Z_to_bv 64 fl)) with (Z_to_bv 64 fl) by (unfold zx32; rewrite unsigned_lit by lia; rewrite Z.mod_small by lia; reflexivity).
step. rewrite (unsigned_lit fl) by lia.
destruct (land1_cases fl) as [F1 | F1]; rewrite F1.
-
step. if_true.
apply evt_RZ_done.
eapply (num_trim HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOLL STRTOULL STRTOD STRDUP n ts0 l txt);
[left; reflexivity | exact STC | exact INV | exact Hl | exact Hst | exact PBC | exact NUM | exact LTXT | exact GOTU | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT].
-
step. if_false.
eapply num_strict; [exact MI | exact TXT0 | exact NUM | exact Hc0 | lia | lia | |].
+ intros a1' a2' a3x a4' a5'. apply evt_RZ_done.
eapply (num_trim HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOLL STRTOULL STRTOD STRDUP n ts0 l txt);
[right; reflexivity | exact STC | exact INV | exact Hl | exact Hst | exact PBC | exact NUM | exact LTXT | exact GOTU | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT].
+
intros a1' a2' a3x a4' a5'. step. step. apply evt_RZ_done.
eapply (KERR ts0 []); [apply (PE_INV_W HIx); exact INV | tdok TDOK | exact FS | exact FRM]. }
stash PB. stash TSK. stash REST. stash Dqpb. stash Dqbuf. stash Dpbbuf. stash Dtkbuf. stash Hdtq. clear LV.
apply rz_evt; [exact MOK|].
tk3_walk 0x22a3c ltac:(try change (zxb c0) with (Z_to_bv 64 (bv_unsigned c0))). step.
destruct (Z.eq_dec (bv_unsigned c0) 45) as [C45 | N45]; [| if_truex; apply TO_TRIM].
if_falsex. step. step.
destruct (Z.eq_dec (Z.of_nat (length txt)) 1) as [L1 | Ln1].
2:{ assert (1 <= Z.of_nat (length txt)).
{ destruct txt; [| cbn; lia]. cbn in Hc0. injection Hc0 as <-. exfalso. change (bv_unsigned b0) with 0 in C45. lia. }
if_truex. apply TO_TRIM. }
if_falsex.
step. change (zxb cb) with (Z_to_bv 64 (bv_unsigned cb)). step.
rewrite (unsigned_lit (bv_unsigned cb)) by lia.
step. step.
pose proof (land_lt_pow2 (bv_unsigned cb) 223 8 ltac:(cbn; lia) ltac:(lia)) as LR. change (2^8) with 256 in LR.
destruct (Z.eq_dec (Z.land (bv_unsigned cb) 223) 73) as [CI | NI]; [| if_truex; apply TO_TRIM].
if_falsex.

clear TO_TRIM PBUF TXT0 RD0. unstash Hdtq.
pose proof (wmono_refl rsegs m) as WM. pose proof (munch_refl [(bse, bse + 32); (tk, tk + 72)] m) as MU.
assert (Hbal : bse mod 16 = 0) by (rewrite Hbse; rewrite Z.add_mod by lia; rewrite Hqal; replace (32 * Z.of_nat depth) with (Z.of_nat depth * 2 * 16) by lia; rewrite Z.mod_mul by lia; reflexivity).
tk3_walk 0x21e14 ltac:(try norm_sx32; try rewrite (unsigned_lit (Z.of_nat depth)) by lia; try rewrite Z.shiftl_mul_pow2 by lia; try change (2 ^ 5) with 32; try replace (q + Z.of_nat depth * 32) with bse by lia).
lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
match goal with H : rw_cells rsegs mc bse _ |- _ => rename H into Lnew end;
match goal with H : rw_cells rsegs mc tk _ |- _ => rename H into TOKnew end;
match goal with H : rw_cells rsegs mc spf _ |- _ => rename H into FRnew end end.
unstash PB. unstash TSK. unstash REST.
set (l' := TL ST_inf (tl_ss l) (tl_cur l) (tl_cs l) (tl_cbs l) (tl_name l) (tl_nbs l)).
set (ts1 := TST depth (lupd levels depth l') co pb pbs (TS isd (Z_to_bv 64 0) (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
assert (HW : Forall (pe_wtq (PEF tk oldl newl len lenr sb spf pmd mxd fl) q) [(bse, bse + 32); (tk, tk + 72)]).
{ apply Forall_cons; [right; cbn [fst snd pf_mxd]; lia|]. apply Forall_cons; [left; left; cbn; lia | apply Forall_nil]. }
apply evt_RZ_done.
eapply (KREDO ts1); [ | | unfold ts1; cbn [t_co pf_mxd]; exact Hco | unfold ts1; cbn [t_co pf_mxd]; exact Hcb | | | | exact FS | exact FRM].
- unfold mredo, mbase, cur_st, cur_ss, ts1. cbn [t_levels t_depth t_co pf_len pf_mxd]. rewrite nth_error_lupd_eq by lia.
unfold l'. cbn [tl_st tl_ss pf_mxd]. rewrite Ess. change (rank ST_inf ST_start) with 7%nat. lia.
- lazymatch goal with |- PE_INV _ _ _ _ _ _ _ ?mc _ _ _ _ _ _ _ _ _ =>
assert (REST1 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo mc md A ts0 errv)
by (eapply (PE_REST_private_write HIx) with (ts := ts0) in REST; [exact REST | exact STC | exact MU | exact WM | assumption | apply pe_wtq_private; exact HW]);
assert (TSK1 : tstack rsegs mc q (lupd levels depth l'))
by (subst bse; eapply (tstack_put rsegs m mc q levels depth l' [(tk, tk + 72)]);
[exact TSK | lia | exact MU | exact WM | intros j Hj Hne; cbn; lia
| unfold srec_cells, l'; cbn [tl_st tl_ss tl_cur tl_name pf_mxd]; exact Lnew]);
assert (PB1 : pbuf rsegs mc pbs pb)
by (eapply (pbuf_wtq HIx) with (ts := ts0); [exact STC | exact (proj1 REST) | exact PB | exact MU | exact WM | exact HW])
end.
split.
+ unfold PE_CORE, ts1. cbn [t_levels t_depth t_co t_pb t_pbs t_x t_obj ts_choff ts_isd ts_stpos ts_err ts_ucs ts_high ts_quote pf_len pf_tk pf_spf pf_mxd].
split; [rewrite lupd_length; exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [unfold tok_cells, tok_cells_g; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd]; exact TOKnew|].
split; [exact PB1|]. split; [exact Hpb|]. split; [exact TSK1 | unfold pe_frame; exact FRnew].
+ destruct REST1 as (HP' & LV' & OBJ' & ST' & ERR' & STR' & PLEN' & SBin' & HPR' & MDV' & JCG').
unfold ts1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
split.
{ match goal with |- HEAP _ _ _ ?L _ _ => replace L with (pe_blocks (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 ts0); [exact HP' |] end.
unfold pe_blocks, tstate_blocks, ts0; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd].
fold l'. rewrite (map_lupd_same lvl_blocks levels depth l' l Hl) by reflexivity. reflexivity. }
split; [| split; [| split; [exact ST' | split; [exact ERR' | split; [exact STR' | split; [exact PLEN' | split; [exact SBin' | split; [exact HPR' | split; [exact MDV' | exact JCG']]]]]]]]].
* cbn [t_levels t_depth pf_mxd]. intros i li Hli. destruct (PeanoNat.Nat.eq_dec i depth) as [-> | NE].
-- rewrite nth_error_lupd_eq in Hli by lia. injection Hli as <-.
eapply lvl_cur_restate with (c' := CNone); [exact (LV' depth l Hl) | rewrite Hst; exact Hmode | | unfold ST_inf; lia | exact SS26 | left; reflexivity].
rewrite Ess. apply val_mode. reflexivity.
-- rewrite nth_error_lupd_neq in Hli by congruence. exact (LV' i li Hli).
* revert OBJ'. unfold cur_st, ts0. cbn [t_levels t_depth t_objs t_objbs t_obj pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn [tl_st l' pf_mxd].
rewrite Hl, Hst. cbn. intros E; exact E.
- unfold NUMC, cur_st, ts1. cbn [t_levels t_depth pf_mxd]. rewrite nth_error_lupd_eq by lia. cbn. intros E. discriminate E.
- unfold SPOK, SPV, cur_st, ts1. cbn [t_levels t_depth t_x t_co ts_stpos pf_mxd]. rewrite ?nth_error_lupd_eq by lia.
repeat match goal with |- _ /\ _ => split end.
all: first [ intros E; cbn in E; discriminate E | intros _; change (bv_unsigned (Z_to_bv 64 0)) with 0; rewrite Zmod_0_l; lia ].
-
unfold ts1, l'. eapply (tdepth_ok_upd ts0 l); [exact TDOK | exact Hl | lia | unfold ts0; cbn [t_depth pf_mxd]; lia | reflexivity].
Qed.
End PeNumPost.

Section PeNumPost2.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis STRTOLL : strtox_stmt strtoll_entry.
Hypothesis STRTOULL : strtox_stmt strtoull_entry.
Hypothesis STRTOD : rstrtod_stmt.
Hypothesis STRDUP : strdup_stmt HIx.
Let LB0 : list blk := LB0 pf LBc.

#[using="MEMMOVE STRTOLL STRTOULL STRTOD STRDUP"] Lemma num_flush :
forall (n : nat) (ts : tstate) (l : tlevel) (co0 : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s4 s9 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
pbufc rsegs m (t_pbs ts) (t_pb ts) [] -> 0 <= co0 <= t_co ts ->
Forall (fun b => numb b = true) (firstn (Z.to_nat (t_co ts - co0)) (skipn (Z.to_nat co0) payload)) ->
bytes_at rsegs me GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
(mbase pf ts + 8 <= n)%nat ->
KALL HIx pf q LBc payload me lo sv T F0 n -> KOUT7 HIx pf q LBc payload me lo sv T F0 -> KERR7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x229f4 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7
s4 (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_sb pf + t_co ts)) s9 s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst PBC Hco0 NUM GOTU Hco Hcb TDOK FS FRM Hn KALL KOUT KERR.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & CHOFF & TOK & PB & Hpb & TSK & FR).
pose proof REST as (HP & LV & OBJ & ST & ERR & STR & PLEN & SBin & HPR & MDV & JCG).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct xx as [isd stpos choff err ucs high quote]; cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in *. subst choff.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold tok_cells, tok_cells_g in TOK. cbn [ts_isd ts_stpos ts_choff ts_err ts_ucs ts_high ts_quote pf_mxd] in TOK. unfold pe_frame in FR. unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
pose proof Hn as Hn0. unfold mbase in Hn. cbn [pf_len t_co pf_mxd] in Hn.
unfold_consts.
set (ts0 := TST depth levels co pb pbs (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs) in *.
set (n0 := co - co0) in *.
set (src := firstn (Z.to_nat n0) (skipn (Z.to_nat co0) payload)) in *.
pose proof (bytes_at_bound _ _ _ _ STR) as SBB.
assert (SRCL : Z.of_nat (length src) = n0) by (unfold src; rewrite length_firstn, length_skipn; lia).
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
apply rz_evt; [exact MOK|].
step.
destruct (Z.eq_dec n0 0) as [Z0 | NZ].
{
rewrite Z0. if_true. apply evt_RZ_done.
assert (Esrc : src = []) by (destruct src; [reflexivity | cbn in SRCL; lia]).
replace (Z_to_bv 64 0) with (Z_to_bv 64 (Z.of_nat (@length byte []))) by reflexivity.
eapply (num_infchk HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOLL STRTOULL STRTOD STRDUP n ts0 l []); [exact STC | exact INV | exact Hl | exact Hst | exact PBC | constructor | cbn; lia | exact GOTU | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn0 | exact KALL | exact KOUT | exact KERR]. }
if_falsex. step. step. step. step.

destruct SBin as [L0 | SBin]; [exfalso; lia|].
pose proof PBC as (buf & bpos & cap & post & Epbs & Lpre & PCORE). cbn [length Z.of_nat pf_mxd] in Lpre. subst bpos. pose proof PCORE as (Hbpos & Hcap & _).
pose proof HP as HP1. unfold pe_blocks, tstate_blocks, ts0 in HP1. cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_mxd] in HP1.
rewrite Epbs in HP1. cbn [app pf_mxd] in HP1.
assert (INbuf : In (buf, cap) ((pb, 16) :: (buf, cap) :: (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0)) by (right; left; reflexivity).
pose proof (payload_sep HIx _ _ _ _ _ _ _ _ buf cap STC HP SBin ltac:(apply in_or_app; left; unfold ts0, tstate_blocks; cbn [t_pbs t_objbs t_levels pf_mxd]; rewrite Epbs; apply in_or_app; left; right; left; reflexivity)) as Hdsb.
cbn [pf_sb pf_len pf_mxd] in Hdsb.
pose proof (bytes_at_sub S4L m sb payload (Z.to_nat co0) (Z.to_nat n0) STR ltac:(lia)) as SRC. cbn [hl_segs S4L pf_mxd] in SRC.
rewrite Z2Nat.id in SRC by lia. fold src in SRC.
stash TSK. clear LV OBJ HPR.
apply evt_RZ_done.
eapply (memappend_cps_c HIx MEMMOVE) with (lo := lo) (b := sb + co0) (n := n0);
[ exact HP1 | exact PCORE | lia | exact SRC | exact SRCL
| left; eapply (payload_crange (PEF _ _ _ _ _ _ _ _ _ _)); [exact SBin | intros bb Hbb; apply in_or_app; right; right; right; exact Hbb | cbn [pf_spf pf_mxd]; rewrite ?unsigned_lit by lia; unfold PE_FRAME; lia | lia | lia | cbn [pf_len pf_mxd]; lia] | lia | lia | lia | .. ]; try alloc_side.
all: try (rewrite ?unsigned_lit by lia; first [exact ST | exact ERR]).
all: try (rewrite ?unsigned_lit by lia; unfold PE_FRAME in *; clia).
intros ms2 md2 (m2 & A2 & r & errv2 & buf' & cap' & RS2 & VM2 & ST2 & HPR2 & ERR2 & HP2 & OUT2).
destruct RS2 as (w0 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & w8 & w9 & w10 & w11 & w12 & w13 & F2 & fc2 & -> & FS2 & FRM2).
cbn [hl_segs hl_tp S4L pf_mxd] in *. rewrite ?(unsigned_lit spf) in ST2 by lia. rewrite ?(unsigned_lit spf) in HPR2 by lia.
set (pbs2 := [(pb, 16); (buf', cap')]).
set (ts2 := TST depth levels co pb pbs2 (TS isd stpos (Z_to_bv 64 co) err ucs high quote) obj objs objbs).
assert (INq2 : In (q, (32 * mxd)) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; right; left; reflexivity).
assert (INtk2 : In (tk, 72) ((objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0))
by (apply in_or_app; right; left; reflexivity).
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in FR; [| left; cbn; lia]. cbn [hl_segs S4L pf_mxd] in FR.
apply (heap_pres_rw_cells S4L _ _ _ _ _ _ HPR2) in TOK; [| eapply client_range_block; [exact INtk2 | lia | cbn; lia]]. cbn [hl_segs S4L pf_mxd] in TOK.
unstash TSK. apply (tstack_pres_g S4L _ _ _ _ _ _ HPR2 INq2) in TSK; [| exact LEN32].
assert (REST2 : PE_REST HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 errv2).
{ eapply (PE_REST_call_pb HIx) with (ts := ts0) (LBc := (objbs ++ concat (map lvl_blocks levels)) ++ (tk, 72) :: (q, (32 * mxd)) :: LB0);
[exact STC | exact REST | exact VM2 | exact HPR2 | unfold ts0; cbn [t_objbs t_levels pf_mxd]; intros bb Hb; apply in_or_app;
apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; left; exact Hb | apply in_app_or in Hb; destruct Hb as [Hb|Hb]; [left; apply in_or_app; right; exact Hb | right; right; right; exact Hb]]
| unfold pe_blocks, tstate_blocks; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_tk pf_md pf_mxd pf_fl]; exact HP2
| exact ST2 | exact ERR2]. }
assert (PBany : pbuf rsegs m2 pbs2 pb).
{ destruct OUT2 as [[_ PBS] | (_ & -> & -> & PC)]; [eapply pbufc_pbuf; exact PBS|].
exists buf, 0, cap, [], post. split; [reflexivity|]. split; [reflexivity | exact PC]. }
assert (INV2 : PE_INV HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LB0 payload me lo m2 md2 A2 ts2 cb j1 j2 utf sv errv2).
{ split; [| exact REST2]. unfold PE_CORE, ts2; cbn. split; [exact LEN32|]. split; [exact D32|]. split; [lia|]. split; [reflexivity|].
split; [exact TOK|]. split; [exact PBany|]. split; [exact Hpb|]. split; [exact TSK | exact FR]. }
pose proof (heap_model_ok _ _ _ _ _ _ HP2) as MOK2.
clear HP1 SRC PBany PCORE HP MOK MI REST.
reenter MOK2.
destruct OUT2 as [[-> PBS2] | (-> & -> & -> & _)].
-
tk3_walk 0x22a14 idtac.
apply evt_RZ_done.
replace (Z_to_bv 64 n0) with (Z_to_bv 64 (Z.of_nat (length src))) by (f_equal; lia).
cbn [firstn app pf_mxd] in PBS2.
eapply (num_infchk HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 STRTOLL STRTOULL STRTOD STRDUP n ts2 l src); [exact STC | exact INV2 | exact Hl | exact Hst | exact PBS2 | exact NUM | cbn [pf_len pf_mxd]; lia | exact GOTU | exact Hco | exact Hcb
| tdok TDOK | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM | exact Hn0 | exact KALL | exact KOUT | exact KERR].
-
replace (Z_to_bv 64 (2^64 - 1)) with (Z_to_bv 64 (-1)) by (apply bv_eq; vm_compute; reflexivity).
tk3_walk 0x23ea4 idtac. apply evt_RZ_done.
eapply (KERR ts2 []); [ | tdok TDOK | eapply fsaved_trans; [exact FS | exact FS2] | apply FRM2; exact FRM].
apply (PE_INV_W HIx). unfold ts2, pbs2. exact INV2.
Qed.
End PeNumPost2.

Section PeNumPost3.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis STRTOLL : strtox_stmt strtoll_entry.
Hypothesis STRTOULL : strtox_stmt strtoull_entry.
Hypothesis STRTOD : rstrtod_stmt.
Hypothesis STRDUP : strdup_stmt HIx.
Let LB0 : list blk := LB0 pf LBc.

#[using="MEMMOVE STRTOLL STRTOULL STRTOD STRDUP"] Lemma num_charchk_nz :
forall (n : nat) (ts : tstate) (l : tlevel) (co0 : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
pbufc rsegs m (t_pbs ts) (t_pb ts) [] -> 0 <= co0 <= t_co ts ->
Forall (fun b => numb b = true) (firstn (Z.to_nat (t_co ts - co0)) (skipn (Z.to_nat co0) payload)) ->
bytes_at rsegs me GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
tdepth_ok ts -> t_depth ts <> 0%nat ->
fsaved F0 F -> frm0 fc ->
(mbase pf ts + 8 <= n)%nat ->
KALL HIx pf q LBc payload me lo sv T F0 n -> KOUT7 HIx pf q LBc payload me lo sv T F0 -> KERR7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x228e0 co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 (Z_to_bv 64 (bv_unsigned cb)) a6 a7
(Z_to_bv 64 q) (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst PBC Hco0 NUM GOTU Hco Hcb TDOK Hdn FS FRM Hn KALL KOUT KERR.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & _).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
pose proof (pe_jtab_num_ro m MI) as JT.
pose proof (bv_unsigned_in_range 8 cb) as CBR. unfold bv_modulus in CBR. cbn in CBR.
set (c := bv_unsigned cb) in *.

assert (KOK : forall r0 r1 r2 r3 r4 r5 r6 r7 u0 u1 u2 u3 u4 u5 u6,
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) u0 u1 u2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
r0 r1 r2 r3 r4 r5 r6 r7 (Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 pb) (Z_to_bv 64 (co - co0)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (Z.of_nat depth)) s10 (Z_to_bv 64 PE_JTAB) u3 u4 u5 u6)
F (Z_to_bv 64 0x229f4) fc None m (seg_rom rsegs))).
{ intros r0 r1 r2 r3 r4 r5 r6 r7 u0 u1 u2 u3 u4 u5 u6. apply evt_RZ_done.
eapply (num_flush HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 MEMMOVE STRTOLL STRTOULL STRTOD STRDUP n
(TST depth levels co pb pbs xx obj objs objbs) l co0);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | cbn [t_co pf_mxd]; lia | exact NUM | exact GOTU | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn | exact KALL | exact KOUT | exact KERR]. }
assert (KBAD : forall r0 r1 r2 r3 r4 r5 r6 r7 u0 u1 u2 u3 u4 u5 u6,
evt rsegs (RZ rsegs md T)
(MS (mkR x1 (Z_to_bv 64 spf) gp (Z_to_bv 64 0x77c00) u0 u1 u2 (Z_to_bv 64 tk) (Z_to_bv 64 oldl)
r0 r1 r2 r3 r4 r5 r6 r7 (Z_to_bv 64 newl) (Z_to_bv 64 lenr) (Z_to_bv 64 q) (Z_to_bv 64 (sb + co0)) (Z_to_bv 64 pb) (Z_to_bv 64 (co - co0)) (Z_to_bv 64 (sb + co)) (Z_to_bv 64 (Z.of_nat depth)) s10 (Z_to_bv 64 PE_JTAB) u3 u4 u5 u6)
F (Z_to_bv 64 0x23e18) fc None m (seg_rom rsegs))).
{ intros r0 r1 r2 r3 r4 r5 r6 r7 u0 u1 u2 u3 u4 u5 u6. tk3_walk 0x23ea4 idtac. apply evt_RZ_done.
eapply (KERR (TST depth levels co pb pbs xx obj objs objbs) []); [apply (PE_INV_W HIx); exact INV | tdok TDOK | exact FS | exact FRM]. }
clear INV REST PBC NUM KALL KOUT KERR.
apply rz_evt; [exact MOK|].
step. step. step.
destruct (Z_lt_dec c 9) as [LT9 | GE9].
-
rewrite <- (zbv_shift64 (c + -9)). if_truex.
step. step. rewrite <- (zbv_shift64 (c + -93)). step. tk3_walk 0x23e18 idtac. apply KBAD.
- destruct (Z_lt_dec 73 c) as [GT73 | LE73].
+
if_truex. step. step.
destruct (Z_lt_dec c 93) as [LT93 | GE93].
* rewrite <- (zbv_shift64 (c + -93)). step. tk3_walk 0x23e18 idtac. apply KBAD.
* destruct (Z_lt_dec 125 c) as [GT125 | LE125].
-- step. tk3_walk 0x23e18 idtac. apply KBAD.
-- step. tk3_walk 0x229d4 idtac. step. step. step. step. step. step.
assert (R : 93 <= c <= 125) by lia.
rewrite (unsigned_lit (c + -93)) by lia.
replace (Z.land (bv_unsigned (Z_to_bv 64 (Z.shiftr 4294971393 ((c + -93) mod 64)))) 1) with (if numfollow c then 1 else 0).
2:{ clear - R. enum_from c 93%Z 33%nat; vm_compute; reflexivity. }
step. destruct (numfollow c) eqn:NF; [tk3_walk 0x229f4 idtac; apply KOK | tk3_walk 0x23e18 idtac; apply KBAD].
+
if_falsex. step.
step. step. step.
try rewrite (unsigned_lit (c + -9)) by lia. try rewrite Z.shiftl_mul_pow2 by lia. try change (2 ^ 2) with 4.
pose proof (bytes_at_read rsegs m 0x1352c pe_jtab_num ((c + -9) * 4) 4 (ro_cells_bytes_at'' _ _ _ _ JT) ltac:(lia)
ltac:(change (length pe_jtab_num) with 260%nat; lia)) as RD.
unfold wa in RD. replace (0x1352c + (c + -9) * 4) with ((c + -9) * 4 + 79148) in RD by lia.
step. step. step.
assert (R : 9 <= c <= 73) by lia.
match goal with |- evt _ _ (MS _ _ ?pc _ _ _ _) =>
replace pc with (Z_to_bv 64 (pe_jt_num c)) end.
2:{ clear - R. enum_from c 9%Z 65%nat; apply bv_eq; vm_compute; reflexivity. }
unfold pe_jt_num. destruct (numfollow c); [apply KOK | apply KBAD].
Qed.
End PeNumPost3.

Section PeNumPost4.
Variable HIx : heap_iface S4L.
Variables (pf : pe_fix) (q : Z) (LBc : list blk) (payload : list byte) (me : word -> option byte) (lo : Z)
(sv : pe_saved) (T : TSet) (F0 : bvmap 5 word).
Hypothesis MEMMOVE : memmove_stmt.
Hypothesis STRTOLL : strtox_stmt strtoll_entry.
Hypothesis STRTOULL : strtox_stmt strtoull_entry.
Hypothesis STRTOD : rstrtod_stmt.
Hypothesis STRDUP : strdup_stmt HIx.
Let LB0 : list blk := LB0 pf LBc.

#[using="MEMMOVE STRTOLL STRTOULL STRTOD STRDUP"] Lemma num_charchk :
forall (n : nat) (ts : tstate) (l : tlevel) (co0 : Z)
(m : word -> option byte) (md : Model) (A : AS S4L HIx)
(cb : byte) (j1 j2 utf : list byte) (errv : word)
(x1 gp t0 t1 t2 a0 a1 a2 a3 a4 a6 a7 s10 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32),
PE_STATIC HIx pf lo ->
PE_INV HIx pf q LB0 payload me lo m md A ts cb j1 j2 utf sv errv ->
nth_error (t_levels ts) (t_depth ts) = Some l -> tl_st l = ST_number ->
pbufc rsegs m (t_pbs ts) (t_pb ts) [] -> 0 <= co0 <= t_co ts ->
Forall (fun b => numb b = true) (firstn (Z.to_nat (t_co ts - co0)) (skipn (Z.to_nat co0) payload)) ->
bytes_at rsegs me GOT_free_userdata (le8 (Z_to_bv 64 (fn_free_userdata S4F))) ->
t_co ts < pf_len pf -> nth_error payload (Z.to_nat (t_co ts)) = Some cb ->
tdepth_ok ts ->
fsaved F0 F -> frm0 fc ->
(mbase pf ts + 8 <= n)%nat ->
KALL HIx pf q LBc payload me lo sv T F0 n -> KOUT7 HIx pf q LBc payload me lo sv T F0 -> KERR7 HIx pf q LBc payload me lo sv T F0 ->
realizes rsegs (mkCfg (pe_ms7 rsegs pf 0x228dc co0 x1 gp t0 t1 t2 a0 a1 a2 a3 a4 (Z_to_bv 64 (bv_unsigned cb)) a6 a7
(Z_to_bv 64 q) (Z_to_bv 64 (t_pb ts)) (Z_to_bv 64 (t_co ts - co0)) (Z_to_bv 64 (pf_sb pf + t_co ts)) (Z_to_bv 64 (Z.of_nat (t_depth ts))) s10 t3 t4 t5 t6 F fc m) md) T.
Proof.
intros until fc. intros STC INV Hl Hst PBC Hco0 NUM GOTU Hco Hcb TDOK FS FRM Hn KALL KOUT KERR.
pose proof STC as (LO & LOS & SPA & HT & SP0 & LEN & SB0 & SBL).
pose proof INV as [CORE REST].
destruct CORE as (LEN32 & D32 & CO & _).
pose proof REST as (HP & _).
destruct ts as [depth levels co pb pbs xx obj objs objbs]; cbn [t_depth t_levels t_co t_pb t_pbs t_x t_obj t_objs t_objbs pf_mxd] in *.
destruct pf as [tk oldl newl len lenr sb spf pmd mxd fl_]; pe_gen fl_; cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
unfold pe_ms7, pe_ms in *. cbn [pf_tk pf_spf pf_sb pf_len pf_lenr pf_oldl pf_newl pf_md pf_mxd pf_fl] in *.
pose proof (heap_model_ok _ _ _ _ _ _ HP) as MOK.
pose proof (heap_mem_inv _ _ _ _ _ _ HP) as MI. cbn [hl_segs S4L pf_mxd] in MI.
apply rz_evt; [exact MOK|].
step.
destruct (Nat.eq_dec depth 0) as [D0 | Dn].
{ subst depth. cbn [Z.of_nat pf_mxd]. if_true. apply evt_RZ_done.
eapply (num_flush HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 MEMMOVE STRTOLL STRTOULL STRTOD STRDUP n
(TST 0 levels co pb pbs xx obj objs objbs) l co0);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | cbn [t_co pf_mxd]; lia | exact NUM | exact GOTU | exact Hco | exact Hcb | tdok TDOK | exact FS | exact FRM | exact Hn | exact KALL | exact KOUT | exact KERR]. }
if_falsex. apply evt_RZ_done.
eapply (num_charchk_nz HIx (PEF tk oldl newl len lenr sb spf pmd mxd fl) q LBc payload me lo sv T F0 MEMMOVE STRTOLL STRTOULL STRTOD STRDUP n
(TST depth levels co pb pbs xx obj objs objbs) l co0);
[exact STC | exact INV | exact Hl | exact Hst | exact PBC | cbn [t_co pf_mxd]; lia | exact NUM | exact GOTU | exact Hco | exact Hcb | tdok TDOK | cbn [t_depth]; exact Dn | exact FS | exact FRM | exact Hn | exact KALL | exact KOUT | exact KERR].
Qed.
End PeNumPost4.

End RC__2.
