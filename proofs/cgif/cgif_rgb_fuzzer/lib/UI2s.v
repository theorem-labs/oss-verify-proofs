(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YK11 YK0i YK0j YK14 YK1b YK1a YK15 YN06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import
YQ0j YQ0c YQ0b YQ03 YQ0i YQ0h YQ09 YQ04 YQ05 YQ0e YQ02.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YO3v YO38 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YP0j YP0g YP0r YP0c.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import UH04 UH07 UH06 UO3m
YI00 YI02 YI01 YI03 YI04 UI1e UI2m UI2r.
From OssFuzzTheorems.Proofs.cgif.cgif_rgb_fuzzer.lib Require Import YN05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section h. Context {fx : YK11.FPState} {rc : YN05.RunCeil}.
Definition RA0 : Z := ubs2_A_cgif_raw_addframe.
Definition PC_A   : Z := RA0 + 0x7c.
Definition PC_B   : Z := RA0 + 0x104.
Definition PC_IC  : Z := RA0 + 0x144.
Definition PC_C   : Z := RA0 + 0x1f0.
Definition PC_IL  : Z := RA0 + 0x21c.
Definition PC_L1  : Z := RA0 + 0x240.
Definition PC_L1X : Z := RA0 + 0x298.
Definition PC_L2  : Z := RA0 + 0x2a8.
Definition PC_L2X : Z := RA0 + 0x318.
Definition PC_L3  : Z := RA0 + 0x324.
Definition PC_L3X : Z := RA0 + 0x384.
Definition PC_L4  : Z := RA0 + 0x390.
Definition PC_L4X : Z := RA0 + 0x3f0.
Definition PC_OK  : Z := RA0 + 0x45c.
Definition PC_EAL : Z := RA0 + 0x304.
Definition PC_ST  : Z := RA0 + 0x41c.
Definition PC_RET : Z := RA0 + 0x420.
Definition PC_T2  : Z := RA0 + 0x4d0.
Definition PC_WDB : Z := RA0 + 0x554.
Definition PC_WDBX: Z := RA0 + 0x570.
Definition PC_T2B : Z := RA0 + 0x578.
Definition PC_L4P : Z := RA0 + 0x384.
Definition PC_T3  : Z := RA0 + 0x580.
Definition RA_FRAME : Z := 144.
Definition AC : Z := alloc_ceiling.
Record ra_cx := mkRC {
c_sp : Z;
c_raw : Z; c_cfp : Z; c_g : Z;
c_lct : Z; c_img : Z; c_fattr : Z; c_w : Z; c_h : Z; c_top : Z; c_left : Z; c_delay : Z; c_slct : Z; c_disp : Z; c_tidx : Z;
c_gct : Z; c_rattr : Z; c_W : Z; c_H : Z; c_sgct : Z; c_loops : Z; c_rcur : Z;
c_gvals : list Z;
c_Nimg : Z; c_rest : list (Z * Z);
c_tp : Z; c_gp : Z;
c_s9 : Z; c_s10 : Z; c_s11 : Z }.
Definition cvals (cx : ra_cx) : list Z :=
[c_lct cx; c_img cx; c_fattr cx; c_w cx; c_h cx; c_top cx; c_left cx; c_delay cx; c_slct cx; c_disp cx; c_tidx cx].
Definition rvals (cx : ra_cx) : list Z :=
[ubs2_A_cgif_writecb; c_g cx; c_gct cx; c_rattr cx; c_W cx; c_H cx; c_sgct cx; c_loops cx; c_rcur cx].
Definition rvals' (cx : ra_cx) (cur : Z) : list Z :=
[ubs2_A_cgif_writecb; c_g cx; c_gct cx; c_rattr cx; c_W cx; c_H cx; c_sgct cx; c_loops cx; cur].
Definition c_spe (cx : ra_cx) : Z := c_sp cx + RA_FRAME.
Definition c_nP (cx : ra_cx) : Z := c_w cx * c_h cx.
Definition c_blocks (cx : ra_cx) : list (Z * Z) :=
(c_raw cx, RAW_SIZE) :: (c_g cx, CGIF_SIZE) :: (c_img cx, c_Nimg cx) :: c_rest cx.
Definition rcx_pre (cx : ra_cx) : Prop :=
c_sp cx mod 16 = 0 /\ alloc_ceiling + 8560 <= c_sp cx /\ c_sp cx + 144 <= c_cfp cx /\ c_cfp cx + 40 <= 2 ^ 63 /\ c_cfp cx mod 8 = 0 /\
4096 <= c_raw cx /\ c_raw cx + 48 <= alloc_ceiling /\ c_raw cx mod 16 = 0 /\
4096 <= c_g cx /\ c_g cx + 96 <= alloc_ceiling /\ c_g cx mod 16 = 0 /\
4096 <= c_img cx /\ c_img cx + c_Nimg cx <= alloc_ceiling /\ c_img cx mod 16 = 0 /\
(c_raw cx + 48 <= c_g cx \/ c_g cx + 96 <= c_raw cx) /\
(c_raw cx + 48 <= c_img cx \/ c_img cx + c_Nimg cx <= c_raw cx) /\
(c_g cx + 96 <= c_img cx \/ c_img cx + c_Nimg cx <= c_g cx) /\
1 <= c_w cx /\ 1 <= c_h cx /\ c_w cx * c_h cx <= 100000000 /\ c_w cx * c_h cx <= c_Nimg cx /\
c_sgct cx <= 256 /\
nth_error (c_gvals cx) CG_wfn = Some ubs2_A_writecb /\ nth_error (c_gvals cx) CG_file = Some 0 /\
c_tp cx = ms_tp ubs2_msyms.
Definition rcx_ok (cx : ra_cx) : Prop := rcx_pre cx /\ c_slct cx <= 256.
Definition objs_at (mem : word -> option byte) (cx : ra_cx) (cur : Z) : Prop :=
obj_at ubs2segs mem (c_cfp cx) LAY_RawFrameConfig (cvals cx) /\
obj_at ubs2segs mem (c_raw cx) LAY_Raw (rvals' cx cur) /\
obj_at ubs2segs mem (c_g cx) LAY_CGIF (c_gvals cx).
Lemma obj_at_range' : forall mem a lay vals,
obj_at ubs2segs mem a lay vals -> forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ (8 * Z.of_N (snd (nth j lay (0, 8%N)))).
Proof.
intros mem a lay. induction lay as [|f lay IH]; intros [|v' vals] H j v Hj; cbn in H; [destruct j; discriminate | destruct H | destruct H |].
destruct H as [[_ Hr] H]. destruct j as [|j]; cbn in Hj |- *; [injection Hj as <-; exact Hr | exact (IH vals H j v Hj)].
Qed.
Definition fields_ok (cx : ra_cx) (cur : Z) : Prop :=
0 <= c_lct cx < 2 ^ 64 /\ 0 <= c_img cx < 2 ^ 64 /\ 0 <= c_fattr cx < 2 ^ 32 /\ 0 <= c_w cx < 65536 /\ 0 <= c_h cx < 65536 /\
0 <= c_top cx < 65536 /\ 0 <= c_left cx < 65536 /\ 0 <= c_delay cx < 65536 /\ 0 <= c_slct cx < 65536 /\
0 <= c_disp cx < 256 /\ 0 <= c_tidx cx < 256 /\
0 <= c_g cx < 2 ^ 64 /\ 0 <= c_gct cx < 2 ^ 64 /\ 0 <= c_rattr cx < 2 ^ 32 /\ 0 <= c_W cx < 65536 /\ 0 <= c_H cx < 65536 /\
0 <= c_sgct cx < 65536 /\ 0 <= c_loops cx < 65536 /\ 0 <= cur < 2 ^ 32 /\
length (c_gvals cx) = 17%nat.
Lemma objs_fields_ok : forall mem cx cur, objs_at mem cx cur -> fields_ok cx cur.
Proof.
intros mem cx cur (HC & HR & HG).
pose proof (obj_at_range' _ _ _ _ HC) as FC. pose proof (obj_at_range' _ _ _ _ HR) as FR.
pose proof (obj_at_length _ _ _ _ _ HG) as LG. cbn in LG.
unfold fields_ok.
Ltac fr F j := let H := fresh in pose proof (F j _ eq_refl) as H; cbn [nth snd LAY_RawFrameConfig LAY_Raw LAY_RawConfig app] in H.
fr FC 0%nat. fr FC 1%nat. fr FC 2%nat. fr FC 3%nat. fr FC 4%nat. fr FC 5%nat. fr FC 6%nat. fr FC 7%nat. fr FC 8%nat. fr FC 9%nat. fr FC 10%nat.
fr FR 1%nat. fr FR 2%nat. fr FR 3%nat. fr FR 4%nat. fr FR 5%nat. fr FR 6%nat. fr FR 7%nat. fr FR 8%nat.
change (2 ^ (8 * 8)) with (2 ^ 64) in *. change (2 ^ (8 * 4)) with (2 ^ 32) in *.
change (2 ^ (8 * 2)) with 65536 in *. change (2 ^ (8 * 1)) with 256 in *.
repeat split; try lia.
Qed.
Lemma objs_at_kept : forall mem mem' cx cur,
objs_at mem cx cur ->
(forall i, 0 <= i < 40 -> mbyte ubs2segs mem' (c_cfp cx + i) = mbyte ubs2segs mem (c_cfp cx + i)) ->
(forall i, 0 <= i < 48 -> mbyte ubs2segs mem' (c_raw cx + i) = mbyte ubs2segs mem (c_raw cx + i)) ->
(forall i, 0 <= i < 96 -> mbyte ubs2segs mem' (c_g cx + i) = mbyte ubs2segs mem (c_g cx + i)) ->
objs_at mem' cx cur.
Proof.
intros mem mem' cx cur (HC & HR & HG) H1 H2 H3. split; [|split].
- eapply (obj_at_transport_range _ _ _ _ _ _ 40); [exact HC | reflexivity | exact H1].
- eapply obj_at_transport_range; [exact HR | exact (proj1 LAY_Raw_ok) | exact H2].
- eapply obj_at_transport_range; [exact HG | exact (proj1 LAY_CGIF_ok) | exact H3].
Qed.
Lemma obj_at_raw_cur : forall mem mem' cx cur cur',
obj_at ubs2segs mem (c_raw cx) LAY_Raw (rvals' cx cur) ->
(forall i, 0 <= i < 40 -> mbyte ubs2segs mem' (c_raw cx + i) = mbyte ubs2segs mem (c_raw cx + i)) ->
val_mem ubs2segs mem' (c_raw cx + 40) 4 cur' -> 0 <= cur' < 2 ^ 32 ->
obj_at ubs2segs mem' (c_raw cx) LAY_Raw (rvals' cx cur').
Proof.
intros mem mem' cx cur cur' HR Hk Hv Hr.
unfold LAY_Raw, LAY_RawConfig, rvals' in *. cbn [obj_at app] in HR |- *.
destruct HR as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
assert (T : forall (f : Z * N) v, field_ok ubs2segs mem (c_raw cx) f v -> 0 <= fst f -> fst f + Z.of_N (snd f) <= 40 ->
field_ok ubs2segs mem' (c_raw cx) f v).
{ intros [o w] v [Hval Hrng] Hlo Hhi. cbn [fst snd] in *. split; [|exact Hrng].
intros k Hkk. pose proof (N_nat_Z w). specialize (Hval k Hkk). cbn [fst snd] in Hval |- *.
etransitivity; [| exact Hval].
replace (c_raw cx + o + Z.of_nat k) with (c_raw cx + (o + Z.of_nat k)) by lia. apply Hk. cbn [fst snd] in Hkk. lia. }
split; [apply T; [exact F0 | cbn; lia | cbn; lia]|].
split; [apply T; [exact F1 | cbn; lia | cbn; lia]|].
split; [apply T; [exact F2 | cbn; lia | cbn; lia]|].
split; [apply T; [exact F3 | cbn; lia | cbn; lia]|].
split; [apply T; [exact F4 | cbn; lia | cbn; lia]|].
split; [apply T; [exact F5 | cbn; lia | cbn; lia]|].
split; [apply T; [exact F6 | cbn; lia | cbn; lia]|].
split; [apply T; [exact F7 | cbn; lia | cbn; lia]|].
split; [|exact I]. split; [exact Hv | change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); exact Hr].
Qed.
Definition lits_RFC : list (option Z) := [None; None; None; None; None; None; None; None; None; None; None].
Definition common_facts : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + 8560) (2^63 - 144) 4); (9%nat, mkAF (CEIL_MIN + 8704) (2^63 - 40) 3); (8%nat, mkAF 4096 (CEIL_MAX - 48) 4);
(44%nat, mkAF 4096 (CEIL_MAX - 96) 4); (33%nat, mkAF 4096 CEIL_MAX 4); (34%nat, mkAF 0 (2^32-1) 0);
(35%nat, mkAF 1 65535 0); (36%nat, mkAF 1 65535 0); (37%nat, mkAF 0 65535 0); (38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 65535 0);
(41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0); (46%nat, mkAF 0 (2^32-1) 0); (49%nat, mkAF 0 256 0); (51%nat, mkAF 0 (2^32-1) 0) ].
Definition common_facts3 : list (nat * afact) :=
[ (2%nat, mkAF (CEIL_MIN + 8560) (2^63 - 144) 4); (8%nat, mkAF 4096 (CEIL_MAX - 48) 4);
(44%nat, mkAF 4096 (CEIL_MAX - 96) 4); (33%nat, mkAF 4096 CEIL_MAX 4); (34%nat, mkAF 0 (2^32-1) 0);
(35%nat, mkAF 1 65535 0); (36%nat, mkAF 1 65535 0); (37%nat, mkAF 0 65535 0); (38%nat, mkAF 0 65535 0); (39%nat, mkAF 0 65535 0);
(41%nat, mkAF 0 255 0); (42%nat, mkAF 0 255 0); (46%nat, mkAF 0 (2^32-1) 0); (49%nat, mkAF 0 256 0); (51%nat, mkAF 0 (2^32-1) 0) ].
Definition R_frameW (fwlo fwhi : Z) (xc : list YQ0b.chunk) : YQ0b.region := YQ0b.mkRegion (Some 2%nat) (-16) 48 fwlo fwhi xc.
Definition R_frame (xc : list YQ0b.chunk) : YQ0b.region := R_frameW (-16) 48 xc.
Definition R_cfg : YQ0b.region := YQ0b.mkRegion (Some 9%nat) 0 40 0 0 (obj_chunks_gen LAY_RawFrameConfig 32 lits_RFC).
Definition R_raw (w : bool) : YQ0b.region :=
YQ0b.mkRegion (Some 8%nat) 0 RAW_SIZE (if w then 40 else 0) (if w then 44 else 0) (obj_chunks_gen LAY_Raw 43 lits_Raw).
Definition R_cgif : YQ0b.region := YQ0b.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 52 lits_CGIF).
Definition ra_ssW (pc : Z) (sr : list sv) (fwlo fwhi : Z) (xc : list YQ0b.chunk) (w : bool) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
mkSS pc sr [R_frameW fwlo fwhi xc; R_cfg; R_raw w; R_cgif] None (mkFacts (fs ++ common_facts) cs al).
Definition ra_ss (pc : Z) (sr : list sv) (xc : list YQ0b.chunk) (w : bool) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
ra_ssW pc sr (-16) 48 xc w fs cs al.
Definition ra_extra (cx : ra_cx) (cur : Z) (more : list Z) : list word :=
map (Z_to_bv 64) (cvals cx) ++ map (Z_to_bv 64) (rvals' cx cur) ++ map (Z_to_bv 64) (c_gvals cx) ++ map (Z_to_bv 64) more.
Definition ra_regs (regs : bvmap 5 word) (cx : ra_cx) : Prop :=
getr regs 2 = Z_to_bv 64 (c_sp cx) /\ getr regs 8 = Z_to_bv 64 (c_raw cx) /\ getr regs 9 = Z_to_bv 64 (c_cfp cx) /\
getr regs 4 = Z_to_bv 64 (c_tp cx) /\ getr regs 3 = Z_to_bv 64 (c_gp cx) /\ getr regs 27 = Z_to_bv 64 (c_s11 cx).
Section l.
Variables (regs : bvmap 5 word) (cx : ra_cx) (cur : Z) (more : list Z).
Let E := Ereg regs (ra_extra cx cur more).
Lemma E_reg : forall (r : reg) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r.
Proof. intros r n H. apply ew_Ereg_nat. exact H. Qed.
Lemma E_cv : forall j v, nth_error (cvals cx) j = Some v -> ew E (32 + j) = Z_to_bv 64 v.
Proof. intros j v Hj. subst E. unfold ra_extra. apply Ereg_vals. exact Hj. Qed.
Lemma E_rv : forall j v, nth_error (rvals' cx cur) j = Some v -> ew E (43 + j) = Z_to_bv 64 v.
Proof.
intros j v Hj. subst E. unfold ra_extra. replace (43 + j)%nat with (32 + (11 + j))%nat by lia. rewrite ew_Ereg_extra.
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map.
replace (11 + j - length (cvals cx))%nat with j by (cbn; lia).
assert (Hl : (j < 9)%nat) by (apply (proj1 (nth_error_Some (rvals' cx cur) j)); rewrite Hj; discriminate).
rewrite app_nth1 by (rewrite length_map; cbn; lia).
apply (nth_error_nth (map (Z_to_bv 64) (rvals' cx cur)) j). apply map_nth_error. exact Hj.
Qed.
Lemma E_gv : length (c_gvals cx) = 17%nat -> forall j v, nth_error (c_gvals cx) j = Some v -> ew E (52 + j) = Z_to_bv 64 v.
Proof.
intros HL j v Hj. subst E. unfold ra_extra. replace (52 + j)%nat with (32 + (20 + j))%nat by lia. rewrite ew_Ereg_extra.
assert (Hl : (j < 17)%nat) by (rewrite <- HL; apply (proj1 (nth_error_Some (c_gvals cx) j)); rewrite Hj; discriminate).
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map.
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map.
replace (20 + j - length (cvals cx) - length (rvals' cx cur))%nat with j by (cbn; lia).
rewrite app_nth1 by (rewrite length_map, HL; exact Hl).
apply (nth_error_nth (map (Z_to_bv 64) (c_gvals cx)) j). apply map_nth_error. exact Hj.
Qed.
Lemma E_more : length (c_gvals cx) = 17%nat -> forall j, ew E (69 + j) = nth j (map (Z_to_bv 64) more) (Z_to_bv 64 0).
Proof.
intros HL j. subst E. unfold ra_extra. replace (69 + j)%nat with (32 + (37 + j))%nat by lia. rewrite ew_Ereg_extra.
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map.
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map.
rewrite app_nth2 by (rewrite length_map, HL; cbn; lia). rewrite length_map, HL.
f_equal. all: cbn; lia.
Qed.
Lemma E_morev : length (c_gvals cx) = 17%nat -> forall j v, nth_error more j = Some v -> ew E (69 + j) = Z_to_bv 64 v.
Proof.
intros HL j v Hj. rewrite (E_more HL j). apply (nth_error_nth (map (Z_to_bv 64) more) j). apply map_nth_error. exact Hj.
Qed.
End l.
Section S.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs2_msyms MR := aa_laws API.
Lemma ra_st_okW : forall cx cur regs more mem pc sr fwlo fwhi w xc fs cs al,
rcx_ok cx -> objs_at mem cx cur -> ra_regs regs cx ->
let E := Ereg regs (ra_extra cx cur more) in
regs_ok E sr regs ->
(forall a, c_sp cx + fwlo <= a < c_sp cx + fwhi -> writable_at ubs2segs mem a) ->
(w = true -> forall a, c_raw cx + 40 <= a < c_raw cx + 44 -> writable_at ubs2segs mem a) ->
region_wf (R_frameW fwlo fwhi xc) = true ->
Forall (chunk_ok ubs2segs E mem (c_sp cx)) xc ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs2segs E (ra_ssW pc sr fwlo fwhi xc w fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs2segs)).
Proof.
intros cx cur regs more mem pc sr fwlo fwhi w xc fs cs al Hcx Hobjs HR E Hsr Hwst Hwraw Hwf Hxc Hfs Hcs Hal. subst E.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (objs_fields_ok _ _ _ Hobjs) as HF.
destruct Hobjs as (OC & OR & OG).
destruct cx as [sp raw cfp g lct img fattr w_ h_ top left delay slct disp tidx gct rattr W H sgct loops rcur gvals Nimg rest tp gp s9v s10v s11v].
unfold rcx_ok, rcx_pre in Hcx. unfold fields_ok in HF. unfold ra_regs in HR.
cbn [c_sp c_raw c_cfp c_g c_lct c_img c_fattr c_w c_h c_top c_left c_delay c_slct c_disp c_tidx
c_gct c_rattr c_W c_H c_sgct c_loops c_rcur c_gvals c_Nimg c_rest c_tp c_gp c_s9 c_s10 c_s11] in *.
destruct Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htp) & Hslct).
destruct HF as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & LG).
destruct HR as (R2 & R8 & R9 & R4 & R3 & R27).
set (cx := mkRC sp raw cfp g lct img fattr w_ h_ top left delay slct disp tidx gct rattr W H sgct loops rcur gvals Nimg rest tp gp s9v s10v s11v) in *.
assert (HE2 : ew (Ereg regs (ra_extra cx cur more)) 2 = Z_to_bv 64 sp) by (rewrite (E_reg regs cx cur more 2%bv 2) by reflexivity; exact R2).
assert (HE8 : ew (Ereg regs (ra_extra cx cur more)) 8 = Z_to_bv 64 raw) by (rewrite (E_reg regs cx cur more 8%bv 8) by reflexivity; exact R8).
assert (HE9 : ew (Ereg regs (ra_extra cx cur more)) 9 = Z_to_bv 64 cfp) by (rewrite (E_reg regs cx cur more 9%bv 9) by reflexivity; exact R9).
pose proof (E_cv regs cx cur more) as HX. pose proof (E_rv regs cx cur more) as HY. pose proof (E_gv regs cx cur more LG) as HZ.
assert (HE44 : ew (Ereg regs (ra_extra cx cur more)) 44 = Z_to_bv 64 g) by (apply (HY 1%nat); reflexivity).
assert (HE33 : ew (Ereg regs (ra_extra cx cur more)) 33 = Z_to_bv 64 img) by (apply (HX 1%nat); reflexivity).
assert (HE34 : ew (Ereg regs (ra_extra cx cur more)) 34 = Z_to_bv 64 fattr) by (apply (HX 2%nat); reflexivity).
assert (HE35 : ew (Ereg regs (ra_extra cx cur more)) 35 = Z_to_bv 64 w_) by (apply (HX 3%nat); reflexivity).
assert (HE36 : ew (Ereg regs (ra_extra cx cur more)) 36 = Z_to_bv 64 h_) by (apply (HX 4%nat); reflexivity).
assert (HE37 : ew (Ereg regs (ra_extra cx cur more)) 37 = Z_to_bv 64 top) by (apply (HX 5%nat); reflexivity).
assert (HE38 : ew (Ereg regs (ra_extra cx cur more)) 38 = Z_to_bv 64 left) by (apply (HX 6%nat); reflexivity).
assert (HE39 : ew (Ereg regs (ra_extra cx cur more)) 39 = Z_to_bv 64 delay) by (apply (HX 7%nat); reflexivity).
assert (HE41 : ew (Ereg regs (ra_extra cx cur more)) 41 = Z_to_bv 64 disp) by (apply (HX 9%nat); reflexivity).
assert (HE42 : ew (Ereg regs (ra_extra cx cur more)) 42 = Z_to_bv 64 tidx) by (apply (HX 10%nat); reflexivity).
assert (HE46 : ew (Ereg regs (ra_extra cx cur more)) 46 = Z_to_bv 64 rattr) by (apply (HY 3%nat); reflexivity).
assert (HE49 : ew (Ereg regs (ra_extra cx cur more)) 49 = Z_to_bv 64 sgct) by (apply (HY 6%nat); reflexivity).
assert (HE51 : ew (Ereg regs (ra_extra cx cur more)) 51 = Z_to_bv 64 cur) by (apply (HY 8%nat); reflexivity).
apply entry_st_ok_full.
- exact Hsr.
- cbn [regions_wf ra_ssW forallb]. rewrite Hwf. destruct w; reflexivity.
- constructor; [|constructor; [|constructor; [|constructor; [|constructor]]]].
+ unfold region_ok, R_frameW. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwst; lia|]. exact Hxc.
+ eapply (region_ok_obj_gen ubs2segs _ mem 9 cfp); [rewrite HE9; apply unsigned_lit_small; lia | lia | lia | exact OC | reflexivity | exact HX | | intros i Hi; lia].
intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
+ eapply (region_ok_obj_gen ubs2segs _ mem 8 raw); [rewrite HE8; apply unsigned_lit_small; lia | lia | lia | exact OR | reflexivity | exact HY | apply lits_Raw_ok; reflexivity |].
intros i Hi. destruct w; [apply (Hwraw eq_refl); lia | lia].
+ eapply (region_ok_obj_gen ubs2segs _ mem 44 g); [rewrite HE44; apply unsigned_lit_small; lia | lia | lia | exact OG | reflexivity | exact HZ | apply (lits_CGIF_ok gvals Hwfn Hfile) | intros i Hi; lia].
- cbn [pairwise_disjoint all_disjoint ra_ssW]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val R_frameW R_cfg R_raw R_cgif].
rewrite HE2, HE9, HE8, HE44, !unsigned_lit_small by lia. unfold RAW_SIZE, CGIF_SIZE. repeat split; lia.
- split; [|split; [exact Hcs | exact Hal]].
unfold ra_ssW. cbn [f_atoms]. apply atoms_ok_app; [exact Hfs|].
cbn [atoms_ok common_facts]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE2, HE9, HE8, HE44, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE41, HE42, HE46, HE49, HE51, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [assumption | lia | idtac].
all: first [ rewrite (Znumtheory.Zmod_div_mod 8 16); [reflexivity | lia | lia | exists 2; reflexivity] | idtac ].
Qed.
Lemma ra_st_ok : forall cx cur regs more mem pc sr w xc fs cs al,
rcx_ok cx -> objs_at mem cx cur -> ra_regs regs cx ->
let E := Ereg regs (ra_extra cx cur more) in
regs_ok E sr regs ->
(forall a, c_sp cx - 16 <= a < c_sp cx + 48 -> writable_at ubs2segs mem a) ->
(w = true -> forall a, c_raw cx + 40 <= a < c_raw cx + 44 -> writable_at ubs2segs mem a) ->
region_wf (R_frame xc) = true ->
Forall (chunk_ok ubs2segs E mem (c_sp cx)) xc ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs2segs E (ra_ss pc sr xc w fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs2segs)).
Proof.
intros cx cur regs more mem pc sr w xc fs cs al Hcx Hobjs HR E Hsr Hwst Hwraw Hwf Hxc Hfs Hcs Hal. subst E.
apply (ra_st_okW cx cur regs more mem pc sr (-16) 48 w xc fs cs al Hcx Hobjs HR Hsr); try assumption; intros a Ha; apply Hwst; lia.
Qed.
Definition ra_ss3W (pc : Z) (sr : list sv) (fwlo fwhi : Z) (xc : list YQ0b.chunk) (w : bool) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
mkSS pc sr [R_frameW fwlo fwhi xc; R_raw w; R_cgif] None (mkFacts (fs ++ common_facts3) cs al).
Definition ra_ss3 (pc : Z) (sr : list sv) (xc : list YQ0b.chunk) (w : bool) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
ra_ss3W pc sr (-16) 48 xc w fs cs al.
Lemma ra_st_ok3W : forall cx cur regs more mem pc sr fwlo fwhi w xc fs cs al,
rcx_ok cx -> objs_at mem cx cur ->
getr regs 2 = Z_to_bv 64 (c_sp cx) -> getr regs 8 = Z_to_bv 64 (c_raw cx) ->
let E := Ereg regs (ra_extra cx cur more) in
regs_ok E sr regs ->
(forall a, c_sp cx + fwlo <= a < c_sp cx + fwhi -> writable_at ubs2segs mem a) ->
(w = true -> forall a, c_raw cx + 40 <= a < c_raw cx + 44 -> writable_at ubs2segs mem a) ->
region_wf (R_frameW fwlo fwhi xc) = true ->
Forall (chunk_ok ubs2segs E mem (c_sp cx)) xc ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs2segs E (ra_ss3W pc sr fwlo fwhi xc w fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs2segs)).
Proof.
intros cx cur regs more mem pc sr fwlo fwhi w xc fs cs al Hcx Hobjs R2 R8 E Hsr Hwst Hwraw Hwf Hxc Hfs Hcs Hal. subst E.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (objs_fields_ok _ _ _ Hobjs) as HF.
destruct Hobjs as (OC & OR & OG).
destruct cx as [sp raw cfp g lct img fattr w_ h_ top left delay slct disp tidx gct rattr W H sgct loops rcur gvals Nimg rest tp gp s9v s10v s11v].
unfold rcx_ok, rcx_pre in Hcx. unfold fields_ok in HF.
cbn [c_sp c_raw c_cfp c_g c_lct c_img c_fattr c_w c_h c_top c_left c_delay c_slct c_disp c_tidx
c_gct c_rattr c_W c_H c_sgct c_loops c_rcur c_gvals c_Nimg c_rest c_tp c_gp c_s9 c_s10 c_s11] in *.
destruct Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htp) & Hslct).
destruct HF as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & LG).
set (cx := mkRC sp raw cfp g lct img fattr w_ h_ top left delay slct disp tidx gct rattr W H sgct loops rcur gvals Nimg rest tp gp s9v s10v s11v) in *.
assert (HE2 : ew (Ereg regs (ra_extra cx cur more)) 2 = Z_to_bv 64 sp) by (rewrite (E_reg regs cx cur more 2%bv 2) by reflexivity; exact R2).
assert (HE8 : ew (Ereg regs (ra_extra cx cur more)) 8 = Z_to_bv 64 raw) by (rewrite (E_reg regs cx cur more 8%bv 8) by reflexivity; exact R8).
pose proof (E_cv regs cx cur more) as HX. pose proof (E_rv regs cx cur more) as HY. pose proof (E_gv regs cx cur more LG) as HZ.
assert (HE44 : ew (Ereg regs (ra_extra cx cur more)) 44 = Z_to_bv 64 g) by (apply (HY 1%nat); reflexivity).
assert (HE33 : ew (Ereg regs (ra_extra cx cur more)) 33 = Z_to_bv 64 img) by (apply (HX 1%nat); reflexivity).
assert (HE34 : ew (Ereg regs (ra_extra cx cur more)) 34 = Z_to_bv 64 fattr) by (apply (HX 2%nat); reflexivity).
assert (HE35 : ew (Ereg regs (ra_extra cx cur more)) 35 = Z_to_bv 64 w_) by (apply (HX 3%nat); reflexivity).
assert (HE36 : ew (Ereg regs (ra_extra cx cur more)) 36 = Z_to_bv 64 h_) by (apply (HX 4%nat); reflexivity).
assert (HE37 : ew (Ereg regs (ra_extra cx cur more)) 37 = Z_to_bv 64 top) by (apply (HX 5%nat); reflexivity).
assert (HE38 : ew (Ereg regs (ra_extra cx cur more)) 38 = Z_to_bv 64 left) by (apply (HX 6%nat); reflexivity).
assert (HE39 : ew (Ereg regs (ra_extra cx cur more)) 39 = Z_to_bv 64 delay) by (apply (HX 7%nat); reflexivity).
assert (HE41 : ew (Ereg regs (ra_extra cx cur more)) 41 = Z_to_bv 64 disp) by (apply (HX 9%nat); reflexivity).
assert (HE42 : ew (Ereg regs (ra_extra cx cur more)) 42 = Z_to_bv 64 tidx) by (apply (HX 10%nat); reflexivity).
assert (HE46 : ew (Ereg regs (ra_extra cx cur more)) 46 = Z_to_bv 64 rattr) by (apply (HY 3%nat); reflexivity).
assert (HE49 : ew (Ereg regs (ra_extra cx cur more)) 49 = Z_to_bv 64 sgct) by (apply (HY 6%nat); reflexivity).
assert (HE51 : ew (Ereg regs (ra_extra cx cur more)) 51 = Z_to_bv 64 cur) by (apply (HY 8%nat); reflexivity).
apply entry_st_ok_full.
- exact Hsr.
- cbn [regions_wf ra_ss3W forallb]. rewrite Hwf. destruct w; reflexivity.
- constructor; [|constructor; [|constructor; [|constructor]]].
+ unfold region_ok, R_frameW. cbn [r_base r_lo r_hi r_wlo r_whi r_chunks base_val].
rewrite HE2, unsigned_lit_small by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; apply Hwst; lia|]. exact Hxc.
+ eapply (region_ok_obj_gen ubs2segs _ mem 8 raw); [rewrite HE8; apply unsigned_lit_small; lia | lia | lia | exact OR | reflexivity | exact HY | apply lits_Raw_ok; reflexivity |].
intros i Hi. destruct w; [apply (Hwraw eq_refl); lia | lia].
+ eapply (region_ok_obj_gen ubs2segs _ mem 44 g); [rewrite HE44; apply unsigned_lit_small; lia | lia | lia | exact OG | reflexivity | exact HZ | apply (lits_CGIF_ok gvals Hwfn Hfile) | intros i Hi; lia].
- cbn [pairwise_disjoint all_disjoint ra_ss3W]. unfold extent_disjoint. cbn [r_base r_lo r_hi base_val R_frameW R_raw R_cgif].
rewrite HE2, HE8, HE44, !unsigned_lit_small by lia. unfold RAW_SIZE, CGIF_SIZE. repeat split; lia.
- split; [|split; [exact Hcs | exact Hal]].
unfold ra_ss3W. cbn [f_atoms]. apply atoms_ok_app; [exact Hfs|].
cbn [atoms_ok common_facts3]. unfold afact_ok, AC. cbn [af_lo af_hi af_al2].
rewrite HE2, HE8, HE44, HE33, HE34, HE35, HE36, HE37, HE38, HE39, HE41, HE42, HE46, HE49, HE51, !unsigned_lit_small by lia.
change (2 ^ 4) with 16. change (2 ^ 3) with 8. change (2 ^ 0) with 1. rewrite !Z.mod_1_r.
repeat split; first [assumption | lia | idtac].
Qed.
Lemma ra_st_ok3 : forall cx cur regs more mem pc sr w xc fs cs al,
rcx_ok cx -> objs_at mem cx cur ->
getr regs 2 = Z_to_bv 64 (c_sp cx) -> getr regs 8 = Z_to_bv 64 (c_raw cx) ->
let E := Ereg regs (ra_extra cx cur more) in
regs_ok E sr regs ->
(forall a, c_sp cx - 16 <= a < c_sp cx + 48 -> writable_at ubs2segs mem a) ->
(w = true -> forall a, c_raw cx + 40 <= a < c_raw cx + 44 -> writable_at ubs2segs mem a) ->
region_wf (R_frame xc) = true ->
Forall (chunk_ok ubs2segs E mem (c_sp cx)) xc ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs2segs E (ra_ss3 pc sr xc w fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs2segs)).
Proof.
intros cx cur regs more mem pc sr w xc fs cs al Hcx Hobjs R2 R8 E Hsr Hwst Hwraw Hwf Hxc Hfs Hcs Hal. subst E.
apply (ra_st_ok3W cx cur regs more mem pc sr (-16) 48 w xc fs cs al Hcx Hobjs R2 R8 Hsr); try assumption; intros a Ha; apply Hwst; lia.
Qed.
End S.
Section p.
Variable B : malloc_syms.
Local Notation segs := (ms_segs B) (only parsing).
Definition SAVEDN (n : nat) : list (reg * Z) := firstn n SAVED.
Definition frame_savedN (n : nat) (regs0 : bvmap 5 word) (m : word -> option byte) (spe : Z) : Prop :=
forall r d, In (r, d) (SAVEDN n) -> word_mem segs m (spe - d) (bv_unsigned (getr regs0 r)).
Lemma SAVEDN_range : forall n r d, (n <= 13)%nat -> In (r, d) (SAVEDN n) -> 8 <= d <= 8 * Z.of_nat n.
Proof.
intros n r d Hn Hin.
do 14 (destruct n as [|n]; [cbv [SAVEDN SAVED firstn In] in Hin;
repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; lia|]); destruct Hin |]).
lia.
Qed.
Lemma frame_savedN_kept : forall n regs0 m m' spe, (n <= 13)%nat ->
frame_savedN n regs0 m spe ->
(forall a, spe - 8 * Z.of_nat n <= a < spe -> mbyte segs m' a = mbyte segs m a) ->
frame_savedN n regs0 m' spe.
Proof.
intros n regs0 m m' spe Hn H Hf r d Hin k Hk.
pose proof (SAVEDN_range n r d Hn Hin) as Hd.
rewrite Hf by lia. apply (H r d Hin). exact Hk.
Qed.
Lemma frame_savedN_of_region : forall n E m regs0 spe cs lo hi wlo whi,
region_ok segs E m (YQ0b.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spe ->
(forall r d, In (r, d) (SAVEDN n) -> exists e, In (mkChunk (- d) (CVal 8 e)) cs /\ sv_denot E e = getr regs0 r) ->
frame_savedN n regs0 m spe.
Proof.
intros n E m regs0 spe cs lo hi wlo whi (_ & _ & _ & Hcs) H2 Hsv r d Hrd.
destruct (Hsv r d Hrd) as (e & Hin & He).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [r_base base_val] in Hc. rewrite H2 in Hc.
pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
apply val_mem_word_mem. replace (spe - d) with (spe + - d) by lia.
exact (val_of_chunk_ok segs E m spe (- d) 8%N e (bv_unsigned (getr regs0 r)) Hc
ltac:(rewrite He; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Definition savedN_vals (n : nat) (regs0 : bvmap 5 word) : list word := map (fun rd => getr regs0 (fst rd)) (SAVEDN n).
Definition saved_chunks_at (n : nat) (fr : Z) (k : nat) : list YQ0b.chunk :=
map (fun jd => mkChunk (fr - snd jd) (CVal 8 (SOff (k + fst jd)%nat 0)))
(combine (seq 0 n) (map snd (SAVEDN n))).
Lemma saved_chunks_at_ok : forall n E m regs0 spe fr k, (n <= 13)%nat ->
(forall j, (j < n)%nat -> ew E (k + j)%nat = nth j (savedN_vals n regs0) (Z_to_bv 64 0)) ->
frame_savedN n regs0 m spe ->
Forall (chunk_ok segs E m (spe - fr)) (saved_chunks_at n fr k).
Proof.
intros n E m regs0 spe fr k Hn HE HF.
unfold saved_chunks_at. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as ([j d] & <- & Hjd).
cbn [fst snd].
assert (Hnth : exists r, nth_error (SAVEDN n) j = Some (r, d)).
{ clear - Hjd Hn.
do 14 (destruct n as [|n]; [cbv [SAVEDN SAVED firstn map snd combine seq] in Hjd;
repeat (destruct Hjd as [Hjd|Hjd]; [inversion Hjd; subst; eexists; reflexivity |]); destruct Hjd |]).
lia. }
destruct Hnth as (r & Hr).
assert (Hj : (j < n)%nat).
{ pose proof (proj1 (nth_error_Some (SAVEDN n) j) ltac:(rewrite Hr; discriminate)) as Hl.
unfold SAVEDN in Hl. rewrite length_firstn in Hl. lia. }
assert (Hin : In (r, d) (SAVEDN n)) by (eapply nth_error_In; exact Hr).
pose proof (HF r d Hin) as W.
pose proof (SAVEDN_range n r d Hn Hin) as Hd.
pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
eapply (chunk_ok_val segs E m (spe - fr) _ 8%N _ (bv_unsigned (getr regs0 r))).
- cbn [sv_denot]. rewrite Z.add_0_r, (HE j Hj).
unfold savedN_vals. erewrite (nth_error_nth _ _ _ (map_nth_error _ _ _ Hr)). cbn [fst]. rewrite Z_to_bv_bv_unsigned. reflexivity.
- cbn. lia.
- cbn. lia.
- replace (spe - fr + (fr - d)) with (spe - d) by lia. apply val_mem_word_mem. exact W.
Qed.
End p.
Definition ra_origin (cx : ra_cx) (regs0 : bvmap 5 word) : Prop :=
spZ regs0 = c_sp cx + 144 /\ getr regs0 4 = Z_to_bv 64 (c_tp cx) /\ getr regs0 3 = Z_to_bv 64 (c_gp cx) /\
YK0s.ret_ok (getr regs0 1) /\ 0 <= c_gp cx < 2 ^ 64 /\
getr regs0 25 = Z_to_bv 64 (c_s9 cx) /\ getr regs0 26 = Z_to_bv 64 (c_s10 cx) /\ getr regs0 27 = Z_to_bv 64 (c_s11 cx).
Section q.
Variable API : AllocAPI ubs2_msyms.
Let MR : MR_t := aa_MR API.
Definition ra_post (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (c' : config) : Prop :=
exists L' A' regs' mem' md' (res rcur' : Z),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs2segs)) md' /\
journal ubs2_msyms MR RAWADD_STK (spZ regs0) [(c_raw cx + 40, c_raw cx + 44)] L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
obj_at ubs2segs mem' (c_raw cx) LAY_Raw (rvals' cx rcur') /\
Permutation (blocks L' A') (blocks L A).
Lemma ra_wr_ok : forall E xc c1 c2 c3 (wlo whi : Z) cx STK sp0 FP bl0 blc,
bv_unsigned (ew E 2) = c_sp cx -> sp0 - STK <= c_sp cx - 16 -> c_sp cx + 48 <= sp0 ->
(whi <= wlo \/ (bv_unsigned (ew E 8) = c_raw cx /\ In (c_raw cx, 48) blc /\ 0 <= wlo /\ whi <= 48 /\
forall a, c_raw cx + wlo <= a < c_raw cx + whi -> inFP FP a)) ->
wr_ok E [YQ0b.mkRegion (Some 2%nat) (-16) 48 (-16) 48 xc; YQ0b.mkRegion (Some 9%nat) 0 40 0 0 c1;
YQ0b.mkRegion (Some 8%nat) 0 RAW_SIZE wlo whi c2; YQ0b.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 c3] STK sp0 FP bl0 blc.
Proof.
intros E xc c1 c2 c3 wlo whi cx STK sp0 FP bl0 blc H2 Hlo Hhi Hraw.
eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
destruct Hraw as [Hro | (H8 & Hin & Hwlo & Hwhi & Hfp)].
- apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; exact Hro|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
- eapply wr_ok_cons_block; [reflexivity | exact H8 | exact Hin | cbn [r_wlo]; exact Hwlo | cbn [r_whi]; exact Hwhi | cbn [r_wlo r_whi]; exact Hfp |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
Qed.
Lemma ra_wr_ok3 : forall E xc c2 c3 (wlo whi : Z) cx STK sp0 FP bl0 blc,
bv_unsigned (ew E 2) = c_sp cx -> sp0 - STK <= c_sp cx - 16 -> c_sp cx + 48 <= sp0 ->
(whi <= wlo \/ (bv_unsigned (ew E 8) = c_raw cx /\ In (c_raw cx, 48) blc /\ 0 <= wlo /\ whi <= 48 /\
forall a, c_raw cx + wlo <= a < c_raw cx + whi -> inFP FP a)) ->
wr_ok E [YQ0b.mkRegion (Some 2%nat) (-16) 48 (-16) 48 xc;
YQ0b.mkRegion (Some 8%nat) 0 RAW_SIZE wlo whi c2; YQ0b.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 c3] STK sp0 FP bl0 blc.
Proof.
intros E xc c2 c3 wlo whi cx STK sp0 FP bl0 blc H2 Hlo Hhi Hraw.
eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
destruct Hraw as [Hro | (H8 & Hin & Hwlo & Hwhi & Hfp)].
- apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; exact Hro|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
- eapply wr_ok_cons_block; [reflexivity | exact H8 | exact Hin | cbn [r_wlo]; exact Hwlo | cbn [r_whi]; exact Hwhi | cbn [r_wlo r_whi]; exact Hfp |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
Qed.
Lemma ra_wr_okW : forall E fwlo fwhi xc c1 c2 c3 (wlo whi : Z) cx STK sp0 FP bl0 blc,
bv_unsigned (ew E 2) = c_sp cx -> sp0 - STK <= c_sp cx - 16 -> c_sp cx + 48 <= sp0 -> (fwlo < fwhi -> -16 <= fwlo /\ fwhi <= 48) ->
(whi <= wlo \/ (bv_unsigned (ew E 8) = c_raw cx /\ In (c_raw cx, 48) blc /\ 0 <= wlo /\ whi <= 48 /\
forall a, c_raw cx + wlo <= a < c_raw cx + whi -> inFP FP a)) ->
wr_ok E [YQ0b.mkRegion (Some 2%nat) (-16) 48 fwlo fwhi xc; YQ0b.mkRegion (Some 9%nat) 0 40 0 0 c1;
YQ0b.mkRegion (Some 8%nat) 0 RAW_SIZE wlo whi c2; YQ0b.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 c3] STK sp0 FP bl0 blc.
Proof.
intros E fwlo fwhi xc c1 c2 c3 wlo whi cx STK sp0 FP bl0 blc H2 Hlo Hhi Hfw Hraw.
eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros Hlt; specialize (Hfw Hlt); lia |].
apply wr_ok_cons_ro; [cbn; lia|].
destruct Hraw as [Hro | (H8 & Hin & Hwlo & Hwhi & Hfp)].
- apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; exact Hro|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
- eapply wr_ok_cons_block; [reflexivity | exact H8 | exact Hin | cbn [r_wlo]; exact Hwlo | cbn [r_whi]; exact Hwhi | cbn [r_wlo r_whi]; exact Hfp |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
Qed.
Lemma ra_wr_ok3W : forall E fwlo fwhi xc c2 c3 (wlo whi : Z) cx STK sp0 FP bl0 blc,
bv_unsigned (ew E 2) = c_sp cx -> sp0 - STK <= c_sp cx - 16 -> c_sp cx + 48 <= sp0 -> (fwlo < fwhi -> -16 <= fwlo /\ fwhi <= 48) ->
(whi <= wlo \/ (bv_unsigned (ew E 8) = c_raw cx /\ In (c_raw cx, 48) blc /\ 0 <= wlo /\ whi <= 48 /\
forall a, c_raw cx + wlo <= a < c_raw cx + whi -> inFP FP a)) ->
wr_ok E [YQ0b.mkRegion (Some 2%nat) (-16) 48 fwlo fwhi xc;
YQ0b.mkRegion (Some 8%nat) 0 RAW_SIZE wlo whi c2; YQ0b.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 c3] STK sp0 FP bl0 blc.
Proof.
intros E fwlo fwhi xc c2 c3 wlo whi cx STK sp0 FP bl0 blc H2 Hlo Hhi Hfw Hraw.
eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros Hlt; specialize (Hfw Hlt); lia |].
destruct Hraw as [Hro | (H8 & Hin & Hwlo & Hwhi & Hfp)].
- apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; exact Hro|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
- eapply wr_ok_cons_block; [reflexivity | exact H8 | exact Hin | cbn [r_wlo]; exact Hwlo | cbn [r_whi]; exact Hwhi | cbn [r_wlo r_whi]; exact Hfp |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
Qed.
End q.
Lemma shiftr_mod_byte : forall v m s, 0 <= s -> s + 8 <= m ->
(Z.shiftr (v mod 2 ^ m) s) mod 2 ^ 8 = (Z.shiftr v s) mod 2 ^ 8.
Proof.
intros v m s Hs Hm. apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma val_of_chunk_ok_mod : forall E mem base off (n : N) (e : sv) v,
chunk_ok ubs2segs E mem base (mkChunk off (CVal n e)) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> (Z.of_N n <= 8) ->
val_mem ubs2segs mem (base + off) (N.to_nat n) (v mod 2 ^ (8 * Z.of_N n)).
Proof.
intros E mem base off n e v H He Hv Hn k Hk. unfold chunk_ok in H. cbn [c_off c_val c_len cv_len] in H.
pose proof (N_nat_Z n) as Hnn.
assert (Hp : 0 < 2 ^ (8 * Z.of_N n)) by (apply Z.pow_pos_nonneg; lia).
pose proof (Z.mod_pos_bound v (2 ^ (8 * Z.of_N n)) Hp) as Hr.
destruct (H (Z.of_nat k) ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. rewrite He in Hb1.
unfold byte_of_word in Hb1. rewrite Z_to_bv_unsigned in Hb1.
unfold bv_wrap, bv_modulus in Hb1. change (2 ^ Z.of_N 64) with (2 ^ 64) in Hb1. rewrite Z.mod_small in Hb1 by lia.
injection Hb1 as <-. rewrite Hb2. f_equal.
rewrite le_byte_small; [| rewrite N_nat_Z; lia | lia].
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with (2 ^ 8).
symmetry. apply shiftr_mod_byte; lia.
Qed.
Lemma U_mulw_small : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 32 -> 0 <= y < 2 ^ 32 -> 0 <= x * y < 2 ^ 31 ->
U E (SMdw M_MUL a b) = x * y.
Proof.
intros E a b x y Hx Hy Rx Ry Rp.
rewrite U_of_S, S_SMdw. cbn [zmd_raw]. rewrite Hx, Hy.
rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small y) by lia.
rewrite swrap32_small by lia. apply wrap64_small. lia.
Qed.
Lemma U_mul_small : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x * y < 2 ^ 64 ->
U E (SMd M_MUL a b) = x * y.
Proof.
intros E a b x y Hx Hy Rx Ry Rp.
rewrite U_SMd. cbn [zmd_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. nia.
Qed.

Definition hideR (P : Prop) : Prop := P.
Lemma hideR_i : forall P : Prop, P -> hideR P. Proof. intros P H; exact H. Qed.
Lemma hideR_e : forall P : Prop, hideR P -> P. Proof. intros P H; exact H. Qed.
Lemma val_mem_mod : forall m a n v, val_mem ubs2segs m a n v <-> val_mem ubs2segs m a n (v mod 2 ^ (8 * Z.of_nat n)).
Proof.
intros m a n v. unfold val_mem, le_byte.
assert (Hp : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
rewrite Z.mod_mod by lia. split; intros H; exact H.
Qed.
Lemma mbyte_eq_of1' : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte ubs2segs m' a = mbyte ubs2segs m a.
Proof. intros m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.
End h.
Ltac not_in_wrange basetac :=
try rewrite unsigned_lit_small by lia;
let r0 := fresh "r0" in let Hq0 := fresh "Hq0" in let Hin0 := fresh "Hin0" in
intros (r0 & Hq0 & Hin0); cbv [In] in Hq0;
repeat (destruct Hq0 as [<- | Hq0];
[ cbn [r_base r_wlo r_whi base_val] in Hin0;
repeat (rewrite ew_havoc_old in Hin0; [|cbv; lia]);
basetac Hin0; try rewrite unsigned_lit_small in Hin0 by lia; lia | ]);
destruct Hq0.
Ltac mem_chain basetac :=
first
[ reflexivity
| lazymatch goal with
| |- ?m' ?x = _ =>
match goal with
| HFx : frame_of _ _ ?m1 m' |- _ =>
transitivity (m1 x); [apply HFx; not_in_wrange basetac | mem_chain basetac]
| HFx : frame_of _ _ ?m1 (ms_mem (mkst _ _ m' _)) |- _ =>
transitivity (m1 x); [apply HFx; not_in_wrange basetac | mem_chain basetac]
| HOx : forall y : word, _ -> m' y = ?m1 y |- _ =>
transitivity (m1 x); [apply HOx; try rewrite unsigned_lit_small by lia; lia | mem_chain basetac]
end
end ].
Ltac mbyte_chain basetac := apply mbyte_eq_of1'; mem_chain basetac.
Ltac reg_U HS r Utac H :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
pose proof (st_ok_reg segs E1 ss1 ms1 r HS) as H; eval_sr_get_in H;
rewrite denot_lit_U in H;
lazymatch type of H with _ = Z_to_bv 64 (U ?E2 ?e) =>
let v := fresh "v" in let Hv := fresh "Hv" in
evar (v : Z); assert (Hv : U E2 e = v); [subst v; Utac | rewrite Hv in H; subst v; clear Hv; cbn [ms_regs mkst] in H] end end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
