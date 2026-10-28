(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YM06 YK0s.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YN3v YN32 YK0w.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0i YO0f YO0x YO0d.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import UH00 UH03 UH02 UN3b
YI06 UI5b YI09 YI08 YI0r YI0o UI1w UI3p UI3t.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI16 YI14 YI13 YI00 UI5c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YO07.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YI0j YI0k.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section h. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Definition RA0 : Z := ubs0_A_cgif_raw_addframe.
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
c_s9 : Z; c_s10 : Z; c_s11 : Z;
c_f : Z }.
Definition cvals (cx : ra_cx) : list Z :=
[c_lct cx; c_img cx; c_fattr cx; c_w cx; c_h cx; c_top cx; c_left cx; c_delay cx; c_slct cx; c_disp cx; c_tidx cx].
Definition rvals (cx : ra_cx) : list Z :=
[ubs0_A_cgif_writecb; c_g cx; c_gct cx; c_rattr cx; c_W cx; c_H cx; c_sgct cx; c_loops cx; c_rcur cx].
Definition rvals' (cx : ra_cx) (cur : Z) : list Z :=
[ubs0_A_cgif_writecb; c_g cx; c_gct cx; c_rattr cx; c_W cx; c_H cx; c_sgct cx; c_loops cx; cur].
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
nth_error (c_gvals cx) CG_wfn = Some 0 /\ nth_error (c_gvals cx) CG_file = Some (c_f cx) /\
c_tp cx = ms_tp ubs0_msyms /\
4096 <= c_f cx /\ c_f cx + FILE_BLOCK <= alloc_ceiling /\ In (c_f cx, FILE_BLOCK) (c_rest cx) /\ c_sp cx + 144 <= 2 ^ 47.
Definition rcx_ok (cx : ra_cx) : Prop := rcx_pre cx /\ c_slct cx <= 256.
Definition objs_at (mem : word -> option byte) (cx : ra_cx) (cur : Z) : Prop :=
obj_at ubs0segs mem (c_cfp cx) LAY_RawFrameConfig (cvals cx) /\
obj_at ubs0segs mem (c_raw cx) LAY_Raw (rvals' cx cur) /\
obj_at ubs0segs mem (c_g cx) LAY_CGIF (c_gvals cx).
Lemma obj_at_range' : forall mem a lay vals,
obj_at ubs0segs mem a lay vals -> forall j v, nth_error vals j = Some v -> 0 <= v < 2 ^ (8 * Z.of_N (snd (nth j lay (0, 8%N)))).
Proof using.
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
Proof using.
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
(forall i, 0 <= i < 40 -> mbyte ubs0segs mem' (c_cfp cx + i) = mbyte ubs0segs mem (c_cfp cx + i)) ->
(forall i, 0 <= i < 48 -> mbyte ubs0segs mem' (c_raw cx + i) = mbyte ubs0segs mem (c_raw cx + i)) ->
(forall i, 0 <= i < 96 -> mbyte ubs0segs mem' (c_g cx + i) = mbyte ubs0segs mem (c_g cx + i)) ->
objs_at mem' cx cur.
Proof using.
intros mem mem' cx cur (HC & HR & HG) H1 H2 H3. split; [|split].
- eapply (obj_at_transport_range _ _ _ _ _ _ 40); [exact HC | reflexivity | exact H1].
- eapply obj_at_transport_range; [exact HR | exact (proj1 LAY_Raw_ok) | exact H2].
- eapply obj_at_transport_range; [exact HG | exact (proj1 LAY_CGIF_ok) | exact H3].
Qed.
Lemma obj_at_raw_cur : forall mem mem' cx cur cur',
obj_at ubs0segs mem (c_raw cx) LAY_Raw (rvals' cx cur) ->
(forall i, 0 <= i < 40 -> mbyte ubs0segs mem' (c_raw cx + i) = mbyte ubs0segs mem (c_raw cx + i)) ->
val_mem ubs0segs mem' (c_raw cx + 40) 4 cur' -> 0 <= cur' < 2 ^ 32 ->
obj_at ubs0segs mem' (c_raw cx) LAY_Raw (rvals' cx cur').
Proof using.
intros mem mem' cx cur cur' HR Hk Hv Hr.
unfold LAY_Raw, LAY_RawConfig, rvals' in *. cbn [obj_at app] in HR |- *.
destruct HR as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & _).
assert (T : forall (f : Z * N) v, field_ok ubs0segs mem (c_raw cx) f v -> 0 <= fst f -> fst f + Z.of_N (snd f) <= 40 ->
field_ok ubs0segs mem' (c_raw cx) f v).
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
Definition R_frameW (fwlo fwhi : Z) (xc : list YP09.chunk) : YP09.region := YP09.mkRegion (Some 2%nat) (-16) 48 fwlo fwhi xc.
Definition R_frame (xc : list YP09.chunk) : YP09.region := R_frameW (-16) 48 xc.
Definition R_cfg : YP09.region := YP09.mkRegion (Some 9%nat) 0 40 0 0 (obj_chunks_gen LAY_RawFrameConfig 32 lits_RFC).
Definition R_raw (w : bool) : YP09.region :=
YP09.mkRegion (Some 8%nat) 0 RAW_SIZE (if w then 40 else 0) (if w then 44 else 0) (obj_chunks_gen LAY_Raw 43 lits_Raw).
Definition R_cgif : YP09.region := YP09.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 (obj_chunks_gen LAY_CGIF 52 lits_CGIF).
Definition ra_ssW (pc : Z) (sr : list sv) (fwlo fwhi : Z) (xc : list YP09.chunk) (w : bool) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
mkSS pc sr [R_frameW fwlo fwhi xc; R_cfg; R_raw w; R_cgif] None (mkFacts (fs ++ common_facts) cs al).
Definition ra_ss (pc : Z) (sr : list sv) (xc : list YP09.chunk) (w : bool) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
ra_ssW pc sr (-16) 48 xc w fs cs al.
Definition ra_extra (cx : ra_cx) (cur : Z) (more : list Z) : list word :=
map (Z_to_bv 64) (cvals cx) ++ map (Z_to_bv 64) (rvals' cx cur) ++ map (Z_to_bv 64) (c_gvals cx) ++ map (Z_to_bv 64) more.
Definition ra_regs (regs : bvmap 5 word) (cx : ra_cx) : Prop :=
getr regs 2 = Z_to_bv 64 (c_sp cx) /\ getr regs 8 = Z_to_bv 64 (c_raw cx) /\ getr regs 9 = Z_to_bv 64 (c_cfp cx) /\
getr regs 4 = Z_to_bv 64 (c_tp cx) /\ getr regs 3 = Z_to_bv 64 (c_gp cx) /\ getr regs 27 = Z_to_bv 64 (c_s11 cx).
Section t.
Variables (regs : bvmap 5 word) (cx : ra_cx) (cur : Z) (more : list Z).
Let E := Ereg regs (ra_extra cx cur more).
Lemma E_reg : forall (r : reg) n, Z.of_nat n = bv_unsigned r -> ew E n = getr regs r.
Proof using cur cx more. intros r n H. apply ew_Ereg_nat. exact H. Qed.
Lemma E_cv : forall j v, nth_error (cvals cx) j = Some v -> ew E (32 + j) = Z_to_bv 64 v.
Proof using cur more regs. intros j v Hj. subst E. unfold ra_extra. apply Ereg_vals. exact Hj. Qed.
Lemma E_rv : forall j v, nth_error (rvals' cx cur) j = Some v -> ew E (43 + j) = Z_to_bv 64 v.
Proof using more regs.
intros j v Hj. subst E. unfold ra_extra. replace (43 + j)%nat with (32 + (11 + j))%nat by lia. rewrite ew_Ereg_extra.
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map.
replace (11 + j - length (cvals cx))%nat with j by (cbn; lia).
assert (Hl : (j < 9)%nat) by (apply (proj1 (nth_error_Some (rvals' cx cur) j)); rewrite Hj; discriminate).
rewrite app_nth1 by (rewrite length_map; cbn; lia).
apply (nth_error_nth (map (Z_to_bv 64) (rvals' cx cur)) j). apply map_nth_error. exact Hj.
Qed.
Lemma E_gv : length (c_gvals cx) = 17%nat -> forall j v, nth_error (c_gvals cx) j = Some v -> ew E (52 + j) = Z_to_bv 64 v.
Proof using cur more regs.
intros HL j v Hj. subst E. unfold ra_extra. replace (52 + j)%nat with (32 + (20 + j))%nat by lia. rewrite ew_Ereg_extra.
assert (Hl : (j < 17)%nat) by (rewrite <- HL; apply (proj1 (nth_error_Some (c_gvals cx) j)); rewrite Hj; discriminate).
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map.
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map.
replace (20 + j - length (cvals cx) - length (rvals' cx cur))%nat with j by (cbn; lia).
rewrite app_nth1 by (rewrite length_map, HL; exact Hl).
apply (nth_error_nth (map (Z_to_bv 64) (c_gvals cx)) j). apply map_nth_error. exact Hj.
Qed.
Lemma E_more : length (c_gvals cx) = 17%nat -> forall j, ew E (69 + j) = nth j (map (Z_to_bv 64) more) (Z_to_bv 64 0).
Proof using cur regs.
intros HL j. subst E. unfold ra_extra. replace (69 + j)%nat with (32 + (37 + j))%nat by lia. rewrite ew_Ereg_extra.
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map.
rewrite app_nth2 by (rewrite length_map; cbn; lia). rewrite length_map.
rewrite app_nth2 by (rewrite length_map, HL; cbn; lia). rewrite length_map, HL.
f_equal. all: cbn; lia.
Qed.
Lemma E_morev : length (c_gvals cx) = 17%nat -> forall j v, nth_error more j = Some v -> ew E (69 + j) = Z_to_bv 64 v.
Proof using cur regs.
intros HL j v Hj. rewrite (E_more HL j). apply (nth_error_nth (map (Z_to_bv 64) more) j). apply map_nth_error. exact Hj.
Qed.
End t.
Section S.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Let LAWS : MR_laws ubs0_msyms MR := aa_laws API.
Lemma ra_st_okW : forall cx cur regs more mem pc sr fwlo fwhi w xc fs cs al,
rcx_ok cx -> objs_at mem cx cur -> ra_regs regs cx ->
let E := Ereg regs (ra_extra cx cur more) in
regs_ok E sr regs ->
(forall a, c_sp cx + fwlo <= a < c_sp cx + fwhi -> writable_at ubs0segs mem a) ->
(w = true -> forall a, c_raw cx + 40 <= a < c_raw cx + 44 -> writable_at ubs0segs mem a) ->
region_wf (R_frameW fwlo fwhi xc) = true ->
Forall (chunk_ok ubs0segs E mem (c_sp cx)) xc ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs0segs E (ra_ssW pc sr fwlo fwhi xc w fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs0segs)).
Proof using.
intros cx cur regs more mem pc sr fwlo fwhi w xc fs cs al Hcx Hobjs HR E Hsr Hwst Hwraw Hwf Hxc Hfs Hcs Hal. subst E.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (objs_fields_ok _ _ _ Hobjs) as HF.
destruct Hobjs as (OC & OR & OG).
destruct cx as [sp raw cfp g lct img fattr w_ h_ top left delay slct disp tidx gct rattr W H sgct loops rcur gvals Nimg rest tp gp s9v s10v s11v fv].
unfold rcx_ok, rcx_pre in Hcx. unfold fields_ok in HF. unfold ra_regs in HR.
cbn [c_sp c_raw c_cfp c_g c_lct c_img c_fattr c_w c_h c_top c_left c_delay c_slct c_disp c_tidx
c_gct c_rattr c_W c_H c_sgct c_loops c_rcur c_gvals c_Nimg c_rest c_tp c_gp c_s9 c_s10 c_s11 c_f] in *.
destruct Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htp & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
destruct HF as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & LG).
destruct HR as (R2 & R8 & R9 & R4 & R3 & R27).
set (cx := mkRC sp raw cfp g lct img fattr w_ h_ top left delay slct disp tidx gct rattr W H sgct loops rcur gvals Nimg rest tp gp s9v s10v s11v fv) in *.
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
+ eapply (region_ok_obj_gen ubs0segs _ mem 9 cfp); [rewrite HE9; apply unsigned_lit_small; lia | lia | lia | exact OC | reflexivity | exact HX | | intros i Hi; lia].
intros j z Hj. do 11 (destruct j as [|j]; [discriminate Hj|]). destruct j; discriminate Hj.
+ eapply (region_ok_obj_gen ubs0segs _ mem 8 raw); [rewrite HE8; apply unsigned_lit_small; lia | lia | lia | exact OR | reflexivity | exact HY | apply lits_Raw_ok; reflexivity |].
intros i Hi. destruct w; [apply (Hwraw eq_refl); lia | lia].
+ eapply (region_ok_obj_gen ubs0segs _ mem 44 g); [rewrite HE44; apply unsigned_lit_small; lia | lia | lia | exact OG | reflexivity | exact HZ | apply (lits_CGIF_ok gvals Hwfn Hfile) | intros i Hi; lia].
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
(forall a, c_sp cx - 16 <= a < c_sp cx + 48 -> writable_at ubs0segs mem a) ->
(w = true -> forall a, c_raw cx + 40 <= a < c_raw cx + 44 -> writable_at ubs0segs mem a) ->
region_wf (R_frame xc) = true ->
Forall (chunk_ok ubs0segs E mem (c_sp cx)) xc ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs0segs E (ra_ss pc sr xc w fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs0segs)).
Proof using.
intros cx cur regs more mem pc sr w xc fs cs al Hcx Hobjs HR E Hsr Hwst Hwraw Hwf Hxc Hfs Hcs Hal. subst E.
apply (ra_st_okW cx cur regs more mem pc sr (-16) 48 w xc fs cs al Hcx Hobjs HR Hsr); try assumption; intros a Ha; apply Hwst; lia.
Qed.
Definition ra_ss3W (pc : Z) (sr : list sv) (fwlo fwhi : Z) (xc : list YP09.chunk) (w : bool) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
mkSS pc sr [R_frameW fwlo fwhi xc; R_raw w; R_cgif] None (mkFacts (fs ++ common_facts3) cs al).
Definition ra_ss3 (pc : Z) (sr : list sv) (xc : list YP09.chunk) (w : bool) (fs : list (nat * afact)) (cs : list acond) (al : list (sv * sv)) : sstate :=
ra_ss3W pc sr (-16) 48 xc w fs cs al.
Lemma ra_st_ok3W : forall cx cur regs more mem pc sr fwlo fwhi w xc fs cs al,
rcx_ok cx -> objs_at mem cx cur ->
getr regs 2 = Z_to_bv 64 (c_sp cx) -> getr regs 8 = Z_to_bv 64 (c_raw cx) ->
let E := Ereg regs (ra_extra cx cur more) in
regs_ok E sr regs ->
(forall a, c_sp cx + fwlo <= a < c_sp cx + fwhi -> writable_at ubs0segs mem a) ->
(w = true -> forall a, c_raw cx + 40 <= a < c_raw cx + 44 -> writable_at ubs0segs mem a) ->
region_wf (R_frameW fwlo fwhi xc) = true ->
Forall (chunk_ok ubs0segs E mem (c_sp cx)) xc ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs0segs E (ra_ss3W pc sr fwlo fwhi xc w fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs0segs)).
Proof using.
intros cx cur regs more mem pc sr fwlo fwhi w xc fs cs al Hcx Hobjs R2 R8 E Hsr Hwst Hwraw Hwf Hxc Hfs Hcs Hal. subst E.
pose proof (proj1 alloc_ceiling_val) as Hac. assert (HRSv : RAW_SIZE = 48) by reflexivity. assert (HGSv : CGIF_SIZE = 96) by reflexivity.
pose proof (objs_fields_ok _ _ _ Hobjs) as HF.
destruct Hobjs as (OC & OR & OG).
destruct cx as [sp raw cfp g lct img fattr w_ h_ top left delay slct disp tidx gct rattr W H sgct loops rcur gvals Nimg rest tp gp s9v s10v s11v fv].
unfold rcx_ok, rcx_pre in Hcx. unfold fields_ok in HF.
cbn [c_sp c_raw c_cfp c_g c_lct c_img c_fattr c_w c_h c_top c_left c_delay c_slct c_disp c_tidx
c_gct c_rattr c_W c_H c_sgct c_loops c_rcur c_gvals c_Nimg c_rest c_tp c_gp c_s9 c_s10 c_s11 c_f] in *.
destruct Hcx as ((Hspal & Hsplo & Hcfplo & Hcfphi & Hcfpal & Hraw0 & Hraw1 & Hraw16 & Hg0 & Hg1 & Hg16 & Himg0 & Himg1 & Himg16 &
Hs1 & Hs2 & Hs3 & Hw1 & Hh1 & HnP & HnP2 & Hsgct & Hwfn & Hfile & Htp & Hf0 & Hf1 & Hfin & Hsp47) & Hslct).
destruct HF as (F0 & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & LG).
set (cx := mkRC sp raw cfp g lct img fattr w_ h_ top left delay slct disp tidx gct rattr W H sgct loops rcur gvals Nimg rest tp gp s9v s10v s11v fv) in *.
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
+ eapply (region_ok_obj_gen ubs0segs _ mem 8 raw); [rewrite HE8; apply unsigned_lit_small; lia | lia | lia | exact OR | reflexivity | exact HY | apply lits_Raw_ok; reflexivity |].
intros i Hi. destruct w; [apply (Hwraw eq_refl); lia | lia].
+ eapply (region_ok_obj_gen ubs0segs _ mem 44 g); [rewrite HE44; apply unsigned_lit_small; lia | lia | lia | exact OG | reflexivity | exact HZ | apply (lits_CGIF_ok gvals Hwfn Hfile) | intros i Hi; lia].
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
(forall a, c_sp cx - 16 <= a < c_sp cx + 48 -> writable_at ubs0segs mem a) ->
(w = true -> forall a, c_raw cx + 40 <= a < c_raw cx + 44 -> writable_at ubs0segs mem a) ->
region_wf (R_frame xc) = true ->
Forall (chunk_ok ubs0segs E mem (c_sp cx)) xc ->
atoms_ok E fs -> conds_ok E cs -> alias_ok E al ->
st_ok ubs0segs E (ra_ss3 pc sr xc w fs cs al) (mkst regs (Z_to_bv 64 pc) mem (seg_rom ubs0segs)).
Proof using.
intros cx cur regs more mem pc sr w xc fs cs al Hcx Hobjs R2 R8 E Hsr Hwst Hwraw Hwf Hxc Hfs Hcs Hal. subst E.
apply (ra_st_ok3W cx cur regs more mem pc sr (-16) 48 w xc fs cs al Hcx Hobjs R2 R8 Hsr); try assumption; intros a Ha; apply Hwst; lia.
Qed.
End S.
Section u.
Variable B : malloc_syms.
Local Notation segs := (ms_segs B) (only parsing).
Definition SAVEDN (n : nat) : list (reg * Z) := firstn n SAVED.
Definition frame_savedN (n : nat) (regs0 : bvmap 5 word) (m : word -> option byte) (spe : Z) : Prop :=
forall r d, In (r, d) (SAVEDN n) -> word_mem segs m (spe - d) (bv_unsigned (getr regs0 r)).
Lemma SAVEDN_range : forall n r d, (n <= 13)%nat -> In (r, d) (SAVEDN n) -> 8 <= d <= 8 * Z.of_nat n.
Proof using.
intros n r d Hn Hin.
do 14 (destruct n as [|n]; [cbv [SAVEDN SAVED firstn In] in Hin;
repeat (destruct Hin as [Hin|Hin]; [inversion Hin; subst; lia|]); destruct Hin |]).
lia.
Qed.
Lemma frame_savedN_kept : forall n regs0 m m' spe, (n <= 13)%nat ->
frame_savedN n regs0 m spe ->
(forall a, spe - 8 * Z.of_nat n <= a < spe -> mbyte segs m' a = mbyte segs m a) ->
frame_savedN n regs0 m' spe.
Proof using.
intros n regs0 m m' spe Hn H Hf r d Hin k Hk.
pose proof (SAVEDN_range n r d Hn Hin) as Hd.
rewrite Hf by lia. apply (H r d Hin). exact Hk.
Qed.
Lemma frame_savedN_of_region : forall n E m regs0 spe cs lo hi wlo whi,
region_ok segs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
bv_unsigned (ew E 2) = spe ->
(forall r d, In (r, d) (SAVEDN n) -> exists e, In (mkChunk (- d) (CVal 8 e)) cs /\ sv_denot E e = getr regs0 r) ->
frame_savedN n regs0 m spe.
Proof using.
intros n E m regs0 spe cs lo hi wlo whi (_ & _ & _ & Hcs) H2 Hsv r d Hrd.
destruct (Hsv r d Hrd) as (e & Hin & He).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [r_base base_val] in Hc. rewrite H2 in Hc.
pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Rw. change (bv_modulus 64) with (2 ^ 64) in Rw.
apply val_mem_word_mem. replace (spe - d) with (spe + - d) by lia.
exact (val_of_chunk_ok segs E m spe (- d) 8%N e (bv_unsigned (getr regs0 r)) Hc
ltac:(rewrite He; symmetry; apply Z_to_bv_bv_unsigned) ltac:(cbn; lia) ltac:(cbn; lia)).
Qed.
Definition savedN_vals (n : nat) (regs0 : bvmap 5 word) : list word := map (fun rd => getr regs0 (fst rd)) (SAVEDN n).
Definition saved_chunks_at (n : nat) (fr : Z) (k : nat) : list YP09.chunk :=
map (fun jd => mkChunk (fr - snd jd) (CVal 8 (SOff (k + fst jd)%nat 0)))
(combine (seq 0 n) (map snd (SAVEDN n))).
Lemma saved_chunks_at_ok : forall n E m regs0 spe fr k, (n <= 13)%nat ->
(forall j, (j < n)%nat -> ew E (k + j)%nat = nth j (savedN_vals n regs0) (Z_to_bv 64 0)) ->
frame_savedN n regs0 m spe ->
Forall (chunk_ok segs E m (spe - fr)) (saved_chunks_at n fr k).
Proof using.
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
End u.
Definition ra_origin (cx : ra_cx) (regs0 : bvmap 5 word) : Prop :=
spZ regs0 = c_sp cx + 144 /\ getr regs0 4 = Z_to_bv 64 (c_tp cx) /\ getr regs0 3 = Z_to_bv 64 (c_gp cx) /\
YK0s.ret_ok (getr regs0 1) /\ 0 <= c_gp cx < 2 ^ 64 /\
getr regs0 25 = Z_to_bv 64 (c_s9 cx) /\ getr regs0 26 = Z_to_bv 64 (c_s10 cx) /\ getr regs0 27 = Z_to_bv 64 (c_s11 cx).
Section b0.
Variable API : AllocAPI ubs0_msyms.
Let MR : MR_t := aa_MR API.
Definition ra_post (FP : list (Z * Z)) (Q : Z -> Z -> Prop) (cx : ra_cx) L A mem md (regs0 : bvmap 5 word) (c' : config) : Prop :=
exists L' A' regs' mem' md' (res rcur' : Z),
c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom ubs0segs)) md' /\
journal ubs0_msyms MR RAWADD_STK (spZ regs0) FP L A mem md L' A' mem' md' /\
regs_preserved regs0 regs' /\ st_init_done A' = true /\
getr regs' 10 = Z_to_bv 64 res /\
obj_at ubs0segs mem' (c_raw cx) LAY_Raw (rvals' cx rcur') /\
Permutation (blocks L' A') (blocks L A) /\
Q res rcur'.
Definition rc_int (v : Z) : Z := if v <? 2 ^ 31 then v else v - 2 ^ 32.
Definition ra_model (cx : ra_cx) (IMGV LCTV : list Z) : Z * list Z :=
YO07.raw_addframe (YO07.flag (c_rattr cx) 1) (c_sgct cx) (rc_int (c_rcur cx)) IMGV (c_fattr cx) (c_w cx) (c_h cx) (c_top cx) (c_left cx)
(c_delay cx) (c_slct cx) LCTV (c_disp cx) (c_tidx cx).
Definition ra_exitQ (cx : ra_cx) (IMGV LCTV : list Z) (res rcur' : Z) : Prop :=
(res = 2 /\ rcur' = 2) \/
(exists code, ra_model cx IMGV LCTV = (code, []) /\ Z_to_bv 64 res = Z_to_bv 64 code /\ rcur' = code mod 2 ^ 32).
Lemma ra_model_prev : forall cx IMGV LCTV, rc_int (c_rcur cx) <> 0 -> rc_int (c_rcur cx) <> 6 -> ra_model cx IMGV LCTV = (rc_int (c_rcur cx), []).
Proof using.
intros cx IMGV LCTV H0 H6. unfold ra_model, YO07.raw_addframe, YO07.R_OK, YO07.R_PENDING.
destruct (Z.eqb_spec (rc_int (c_rcur cx)) 0) as [E|_]; [contradiction|]. destruct (Z.eqb_spec (rc_int (c_rcur cx)) 6) as [E|_]; [contradiction|]. reflexivity.
Qed.
Lemma ra_model_badlct : forall cx IMGV LCTV, (c_rcur cx = 0 \/ c_rcur cx = 6) -> 256 < c_slct cx -> ra_model cx IMGV LCTV = (-1, []).
Proof using.
intros cx IMGV LCTV Hr Hs. unfold ra_model, YO07.raw_addframe, YO07.R_OK, YO07.R_PENDING, YO07.R_ERROR.
replace (256 <? c_slct cx) with true by (symmetry; apply Z.ltb_lt; exact Hs). destruct Hr as [-> | ->]; reflexivity.
Qed.
Lemma exitQ_prev : forall cx IMGV LCTV (a0 : word), c_rcur cx <> 0 -> c_rcur cx <> 6 -> 0 <= c_rcur cx < 2 ^ 32 ->
bv_unsigned a0 = (if c_rcur cx <? 2 ^ 31 then c_rcur cx else c_rcur cx - 2 ^ 32 + 2 ^ 64) -> ra_exitQ cx IMGV LCTV (bv_unsigned a0) (c_rcur cx).
Proof using.
intros cx IMGV LCTV a0 H0 H6 Hr Ha. right. exists (rc_int (c_rcur cx)).
assert (Hne : rc_int (c_rcur cx) <> 0 /\ rc_int (c_rcur cx) <> 6) by (unfold rc_int; destruct (Z.ltb_spec (c_rcur cx) (2 ^ 31)); lia).
split; [apply ra_model_prev; tauto|]. rewrite Ha. unfold rc_int.
destruct (Z.ltb_spec (c_rcur cx) (2 ^ 31)) as [Hlo | Hhi].
- split; [reflexivity | rewrite Z.mod_small; lia].
- split.
+ apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
replace (c_rcur cx - 2 ^ 32 + 2 ^ 64) with (c_rcur cx - 2 ^ 32 + 1 * 2 ^ 64) by lia. rewrite Z_mod_plus_full. reflexivity.
+ replace (c_rcur cx - 2 ^ 32) with (c_rcur cx + (-1) * 2 ^ 32) by lia. rewrite Z_mod_plus_full, Z.mod_small; lia.
Qed.
Lemma exitQ_badlct : forall cx IMGV LCTV (r : word), (c_rcur cx = 0 \/ c_rcur cx = 6) -> 256 < c_slct cx -> bv_unsigned r = 2 ^ 64 - 1 ->
ra_exitQ cx IMGV LCTV (bv_unsigned r) (bv_unsigned r mod 2 ^ 32).
Proof using.
intros cx IMGV LCTV r Hr Hs Hv. right. exists (-1). split; [apply ra_model_badlct; assumption|]. rewrite Hv. split; [apply bv_eq; reflexivity | reflexivity].
Qed.
Lemma exitQ_ealloc : forall cx IMGV LCTV (r : word), bv_unsigned r = 2 -> ra_exitQ cx IMGV LCTV (bv_unsigned r) (bv_unsigned r mod 2 ^ 32).
Proof using. intros cx IMGV LCTV r Hv. left. rewrite Hv. split; reflexivity. Qed.
Definition ra_ne (cx : ra_cx) : Z := num_eff (YO07.flag (c_rattr cx) 1) (c_fattr cx) (c_sgct cx) (c_slct cx) (c_tidx cx).
Definition ra_iclen (cx : ra_cx) : Z := YO07.calcInitCodeLen (ra_ne cx).
Definition ra_pix (cx : ra_cx) (IMGV : list Z) : list Z := if YO07.flag (c_fattr cx) 2 then YO07.interlace (c_w cx) IMGV else IMGV.
Definition ra_gce (cx : ra_cx) : list Z :=
if YO07.flag (c_rattr cx) 1 || YO07.flag (c_fattr cx) 1
then [33; 249; 4; (if YO07.flag (c_fattr cx) 1 then Z.lor (c_disp cx mod 256) 1 else c_disp cx mod 256)] ++ YO07.u16le (c_delay cx) ++
[(if YO07.flag (c_fattr cx) 1 then c_tidx cx else 0); 0]
else [].
Definition ra_packed (cx : ra_cx) : Z :=
(if negb (c_slct cx =? 0) then 128 + (YO07.pal_pow (c_slct cx) - 1) else 0) + (if YO07.flag (c_fattr cx) 2 then 64 else 0).
Definition ra_hdr (cx : ra_cx) : list Z :=
[44] ++ YO07.u16le (c_left cx) ++ YO07.u16le (c_top cx) ++ YO07.u16le (c_w cx) ++ YO07.u16le (c_h cx) ++ [ra_packed cx].
Definition ra_lctb (cx : ra_cx) (LCTV : list Z) : list Z :=
if negb (c_slct cx =? 0) then firstn (Z.to_nat (c_slct cx * 3)) LCTV ++ YO07.zeros (((2 ^ YO07.pal_pow (c_slct cx) - c_slct cx) * 3) mod 65536) else [].
Lemma ra_model_lzw : forall cx IMGV LCTV, (c_rcur cx = 0 \/ c_rcur cx = 6) -> c_slct cx <= 256 ->
ra_model cx IMGV LCTV =
match YO07.lzw_stream (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) with
| None => (5, [])
| Some raster => (0, ra_gce cx ++ ra_hdr cx ++ ra_lctb cx LCTV ++ [ra_iclen cx - 1] ++ raster)
end.
Proof using.
intros cx IMGV LCTV Hr Hs. unfold ra_model, YO07.raw_addframe.
assert (E1 : negb (rc_int (c_rcur cx) =? YO07.R_OK) && negb (rc_int (c_rcur cx) =? YO07.R_PENDING) = false)
by (unfold rc_int, YO07.R_OK, YO07.R_PENDING; destruct Hr as [-> | ->]; reflexivity).
rewrite E1. replace (256 <? c_slct cx) with false by (symmetry; apply Z.ltb_ge; lia).
unfold ra_iclen, ra_ne, num_eff, ra_pix, ra_gce, ra_hdr, ra_packed, ra_lctb.
destruct (YO07.lzw_stream _ _ _); [| reflexivity]. unfold YO07.R_OK, YO07.R_EINDEX. rewrite <- !app_assoc. reflexivity.
Qed.
Lemma exitQ_eindex : forall cx IMGV LCTV (r : word), (c_rcur cx = 0 \/ c_rcur cx = 6) -> c_slct cx <= 256 ->
YO07.lzw_stream (2 ^ (ra_iclen cx - 1)) (ra_iclen cx) (ra_pix cx IMGV) = None -> bv_unsigned r = 5 ->
ra_exitQ cx IMGV LCTV (bv_unsigned r) (bv_unsigned r mod 2 ^ 32).
Proof using. intros cx IMGV LCTV r Hr Hs Hn Hv. right. exists 5. rewrite (ra_model_lzw cx IMGV LCTV Hr Hs), Hn, Hv. split; [reflexivity | split; reflexivity]. Qed.
Lemma ra_wr_ok : forall E xc c1 c2 c3 (wlo whi : Z) cx STK sp0 FP bl0 blc,
bv_unsigned (ew E 2) = c_sp cx -> sp0 - STK <= c_sp cx - 16 -> c_sp cx + 48 <= sp0 ->
(whi <= wlo \/ (bv_unsigned (ew E 8) = c_raw cx /\ In (c_raw cx, 48) blc /\ 0 <= wlo /\ whi <= 48 /\
forall a, c_raw cx + wlo <= a < c_raw cx + whi -> inFP FP a)) ->
wr_ok E [YP09.mkRegion (Some 2%nat) (-16) 48 (-16) 48 xc; YP09.mkRegion (Some 9%nat) 0 40 0 0 c1;
YP09.mkRegion (Some 8%nat) 0 RAW_SIZE wlo whi c2; YP09.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 c3] STK sp0 FP bl0 blc.
Proof using.
intros E xc c1 c2 c3 wlo whi cx STK sp0 FP bl0 blc H2 Hlo Hhi Hraw.
eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
apply wr_ok_cons_ro; [cbn; lia|].
destruct Hraw as [Hro | (H8 & Hin & Hwlo & Hwhi & Hfp)].
- apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; exact Hro|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
- eapply wr_ok_cons_block; [reflexivity | exact H8 | exact Hin | cbn [r_wlo]; exact Hwlo | cbn [r_whi]; exact Hwhi | cbn [r_wlo r_whi]; exact Hfp |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
Qed.
Lemma ra_wr_okW : forall E fwlo fwhi xc c1 c2 c3 (wlo whi : Z) cx STK sp0 FP bl0 blc,
bv_unsigned (ew E 2) = c_sp cx -> sp0 - STK <= c_sp cx - 16 -> c_sp cx + 48 <= sp0 -> (fwlo < fwhi -> -16 <= fwlo /\ fwhi <= 48) ->
(whi <= wlo \/ (bv_unsigned (ew E 8) = c_raw cx /\ In (c_raw cx, 48) blc /\ 0 <= wlo /\ whi <= 48 /\
forall a, c_raw cx + wlo <= a < c_raw cx + whi -> inFP FP a)) ->
wr_ok E [YP09.mkRegion (Some 2%nat) (-16) 48 fwlo fwhi xc; YP09.mkRegion (Some 9%nat) 0 40 0 0 c1;
YP09.mkRegion (Some 8%nat) 0 RAW_SIZE wlo whi c2; YP09.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 c3] STK sp0 FP bl0 blc.
Proof using.
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
wr_ok E [YP09.mkRegion (Some 2%nat) (-16) 48 fwlo fwhi xc;
YP09.mkRegion (Some 8%nat) 0 RAW_SIZE wlo whi c2; YP09.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 c3] STK sp0 FP bl0 blc.
Proof using.
intros E fwlo fwhi xc c2 c3 wlo whi cx STK sp0 FP bl0 blc H2 Hlo Hhi Hfw Hraw.
eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros Hlt; specialize (Hfw Hlt); lia |].
destruct Hraw as [Hro | (H8 & Hin & Hwlo & Hwhi & Hfp)].
- apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; exact Hro|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
- eapply wr_ok_cons_block; [reflexivity | exact H8 | exact Hin | cbn [r_wlo]; exact Hwlo | cbn [r_whi]; exact Hwhi | cbn [r_wlo r_whi]; exact Hfp |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
Qed.
Lemma ra_wr_ok3 : forall E xc c2 c3 (wlo whi : Z) cx STK sp0 FP bl0 blc,
bv_unsigned (ew E 2) = c_sp cx -> sp0 - STK <= c_sp cx - 16 -> c_sp cx + 48 <= sp0 ->
(whi <= wlo \/ (bv_unsigned (ew E 8) = c_raw cx /\ In (c_raw cx, 48) blc /\ 0 <= wlo /\ whi <= 48 /\
forall a, c_raw cx + wlo <= a < c_raw cx + whi -> inFP FP a)) ->
wr_ok E [YP09.mkRegion (Some 2%nat) (-16) 48 (-16) 48 xc;
YP09.mkRegion (Some 8%nat) 0 RAW_SIZE wlo whi c2; YP09.mkRegion (Some 44%nat) 0 CGIF_SIZE 0 0 c3] STK sp0 FP bl0 blc.
Proof using.
intros E xc c2 c3 wlo whi cx STK sp0 FP bl0 blc H2 Hlo Hhi Hraw.
eapply wr_ok_cons_win; [reflexivity | exact H2 | cbn [r_wlo r_whi]; intros _; lia |].
destruct Hraw as [Hro | (H8 & Hin & Hwlo & Hwhi & Hfp)].
- apply wr_ok_cons_ro; [cbn [r_wlo r_whi]; exact Hro|]. apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
- eapply wr_ok_cons_block; [reflexivity | exact H8 | exact Hin | cbn [r_wlo]; exact Hwlo | cbn [r_whi]; exact Hwhi | cbn [r_wlo r_whi]; exact Hfp |].
apply wr_ok_cons_ro; [cbn; lia|]. apply wr_ok_nil.
Qed.
End b0.
Lemma lor_range : forall k a b, 0 <= a < 2 ^ k -> 0 <= b < 2 ^ k -> 0 <= Z.lor a b < 2 ^ k.
Proof using.
intros k a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec (Z.lor a b) 0) as [-> | Hnz]; [lia|]. assert (Hk : 0 <= k) by (destruct (Z.lt_ge_cases k 0) as [Hk|Hk]; [rewrite (Z.pow_neg_r 2 k Hk) in Ha; lia | exact Hk]).
apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg a b); lia|]. rewrite Z.log2_lor by lia.
assert (Hk1 : 0 < k) by (destruct (Z.eq_dec k 0) as [Hk0|]; [exfalso; apply Hnz; subst k; change (2 ^ 0) with 1 in Ha, Hb; replace a with 0 by lia; replace b with 0 by lia; reflexivity | lia]).
apply Z.max_lub_lt.
- destruct (Z.eq_dec a 0) as [-> | NE]; [cbn; lia | apply Z.log2_lt_pow2; lia].
- destruct (Z.eq_dec b 0) as [-> | NE]; [cbn; lia | apply Z.log2_lt_pow2; lia].
Qed.
Lemma packed_byte : forall slct fattr p, 0 <= fattr -> 0 <= slct -> (slct <> 0 -> 1 <= p <= 8 /\ p = YO07.pal_pow slct) ->
(Z.lor (if slct =? 0 then 0 else 2 ^ 64 - 128 + (p - 1)) (Z.shiftl (Z.land fattr 2) 5)) mod 2 ^ 8 =
(if negb (slct =? 0) then 128 + (YO07.pal_pow slct - 1) else 0) + (if YO07.flag fattr 2 then 64 else 0).
Proof using.
intros slct fattr p Hf Hs Hp.
assert (Hb : Z.testbit (Z.land fattr 2) 0 = false) by (rewrite Z.land_spec; cbn; apply Bool.andb_false_r).
assert (Hhi : forall n, 2 <= n -> Z.testbit (Z.land fattr 2) n = false).
{ intros n Hn. rewrite Z.land_spec. replace (Z.testbit 2 n) with false; [apply Bool.andb_false_r|]. symmetry. apply Z.bits_above_log2; [lia|]. cbn. lia. }
assert (L2 : Z.land fattr 2 = 0 \/ Z.land fattr 2 = 2).
{ destruct (Z.testbit (Z.land fattr 2) 1) eqn:B1.
- right. apply Z.bits_inj'. intros n Hn. destruct (Z.eq_dec n 0) as [->|]; [rewrite Hb; reflexivity|]. destruct (Z.eq_dec n 1) as [->|]; [rewrite B1; reflexivity|].
rewrite Hhi by lia. symmetry. apply Z.bits_above_log2; [lia|cbn; lia].
- left. apply Z.bits_inj'. intros n Hn. rewrite Z.bits_0. destruct (Z.eq_dec n 0) as [->|]; [exact Hb|]. destruct (Z.eq_dec n 1) as [->|]; [exact B1|]. apply Hhi. lia. }
unfold YO07.flag. destruct (Z.eqb_spec slct 0) as [Hz | Hnz].
- cbn [negb]. destruct L2 as [-> | ->]; reflexivity.
- destruct (Hp Hnz) as [Hp8 <-]. cbn [negb].
assert (C : p = 1 \/ p = 2 \/ p = 3 \/ p = 4 \/ p = 5 \/ p = 6 \/ p = 7 \/ p = 8) by lia.
destruct L2 as [-> | ->]; destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; reflexivity.
Qed.
Lemma packed_byte_cx : forall cx cur p, fields_ok cx cur -> (c_slct cx <> 0 -> 1 <= p <= 8 /\ p = YO07.pal_pow (c_slct cx)) ->
(Z.lor (if c_slct cx =? 0 then 0 else 2 ^ 64 - 128 + (p - 1)) (Z.shiftl (Z.land (c_fattr cx) 2) 5)) mod 2 ^ 8 = ra_packed cx.
Proof using. intros cx cur p HF Hp. unfold ra_packed. apply packed_byte; [| | exact Hp]; pose proof HF as (_ & _ & F2 & _ & _ & _ & _ & _ & F8 & _); lia. Qed.
Lemma st_ok_pin_regR : forall segs E ss ms (r : reg) z,
st_ok segs E ss ms -> getr (ms_regs ms) r = Z_to_bv 64 z -> bv_eqb r 0 = false ->
st_ok segs E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r (SLit z)) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof using.
intros segs E ss ms r z HS Hr Hr0. apply st_ok_regs; [exact HS|].
intros rr. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. cbn [sv_denot]. rewrite <- (st_ok_reg segs E ss ms r HS), Hr. reflexivity.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.
Definition fb37 (mem : word -> option byte) (cx : ra_cx) : Prop := val_mem ubs0segs mem (c_sp cx + 37) 1 44.
Definition fb46 (mem : word -> option byte) (cx : ra_cx) : Prop := val_mem ubs0segs mem (c_sp cx + 46) 1 (ra_packed cx).
Definition fb7 (mem : word -> option byte) (cx : ra_cx) : Prop := val_mem ubs0segs mem (c_sp cx + 7) 1 (ra_iclen cx - 1).
Definition fbC (mem : word -> option byte) (cx : ra_cx) : Prop :=
fb7 mem cx /\ fb37 mem cx /\
val_mem ubs0segs mem (c_sp cx + 38) 2 (c_left cx) /\ val_mem ubs0segs mem (c_sp cx + 40) 2 (c_top cx) /\
val_mem ubs0segs mem (c_sp cx + 42) 2 (c_w cx) /\ val_mem ubs0segs mem (c_sp cx + 44) 2 (c_h cx) /\ fb46 mem cx.
Definition ch37 : YP09.chunk := mkChunk 37 (CVal 1 (SLit 44)).
Definition ch46 (k46 : nat) : YP09.chunk := mkChunk 46 (CVal 1 (SOff k46 0)).
Definition ch7 (k7 : nat) : YP09.chunk := mkChunk 7 (CVal 1 (SOff k7 0)).
Definition chC (k7 k46 : nat) : list YP09.chunk :=
[ch7 k7; ch37; mkChunk 38 (CVal 2 (SOff 38 0)); mkChunk 40 (CVal 2 (SOff 37 0)); mkChunk 42 (CVal 2 (SOff 35 0)); mkChunk 44 (CVal 2 (SOff 36 0)); ch46 k46].
Lemma fb_kept1 : forall mem mem' a n v, val_mem ubs0segs mem a n v -> (forall x, a <= x < a + Z.of_nat n -> mbyte ubs0segs mem' x = mbyte ubs0segs mem x) -> val_mem ubs0segs mem' a n v.
Proof using. intros mem mem' a n v H K k Hk. rewrite K by lia. apply H. exact Hk. Qed.
Lemma fbC_kept : forall mem mem' cx, fbC mem cx ->
(forall x, c_sp cx + 7 <= x < c_sp cx + 8 -> mbyte ubs0segs mem' x = mbyte ubs0segs mem x) ->
(forall x, c_sp cx + 37 <= x < c_sp cx + 47 -> mbyte ubs0segs mem' x = mbyte ubs0segs mem x) -> fbC mem' cx.
Proof using.
intros mem mem' cx (A & B & C & D & E & F & G) K7 K. unfold fbC, fb7, fb37, fb46 in *.
repeat split; (eapply fb_kept1; [eassumption | intros x Hx; first [apply K7; cbn in Hx; lia | apply K; cbn in Hx; lia]]).
Qed.
Lemma ch37_ok : forall E mem cx, fb37 mem cx -> chunk_ok ubs0segs E mem (c_sp cx) ch37.
Proof using. intros E mem cx H. eapply chunk_ok_val; [reflexivity | cbn; lia | cbn; lia | exact H]. Qed.
Lemma ch46_ok : forall E mem cx k46, ew E k46 = Z_to_bv 64 (ra_packed cx) -> 0 <= ra_packed cx < 256 -> fb46 mem cx -> chunk_ok ubs0segs E mem (c_sp cx) (ch46 k46).
Proof using. intros E mem cx k46 Hk Hr H. eapply chunk_ok_val; [cbn [sv_denot]; rewrite Hk, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact H]. Qed.
Lemma ch7_ok : forall E mem cx k7, ew E k7 = Z_to_bv 64 (ra_iclen cx - 1) -> 0 <= ra_iclen cx - 1 < 256 -> fb7 mem cx -> chunk_ok ubs0segs E mem (c_sp cx) (ch7 k7).
Proof using. intros E mem cx k7 Hk Hr H. eapply chunk_ok_val; [cbn [sv_denot]; rewrite Hk, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact H]. Qed.
Lemma chC_ok : forall E mem cx cur k7 k46, fields_ok cx cur ->
ew E 35 = Z_to_bv 64 (c_w cx) -> ew E 36 = Z_to_bv 64 (c_h cx) -> ew E 37 = Z_to_bv 64 (c_top cx) -> ew E 38 = Z_to_bv 64 (c_left cx) ->
ew E k7 = Z_to_bv 64 (ra_iclen cx - 1) -> 0 <= ra_iclen cx - 1 < 256 -> ew E k46 = Z_to_bv 64 (ra_packed cx) -> 0 <= ra_packed cx < 256 ->
fbC mem cx -> Forall (chunk_ok ubs0segs E mem (c_sp cx)) (chC k7 k46).
Proof using.
intros E mem cx cur k7 k46 HF H35 H36 H37 H38 Hk7 R7 Hk46 R46 (A & B & C & D & G & F & I).
pose proof HF as (_ & _ & _ & Fw & Fh & Ftop & Fleft & _).
constructor; [apply ch7_ok; assumption|]. constructor; [apply ch37_ok; assumption|].
constructor; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite H38, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact C]|].
constructor; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite H37, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact D]|].
constructor; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite H35, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact G]|].
constructor; [eapply chunk_ok_val; [cbn [sv_denot]; rewrite H36, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia | exact F]|].
constructor; [apply ch46_ok; assumption|]. constructor.
Qed.
Lemma fb_of_region : forall E m flo fhi fwlo fwhi xc sp off (n : N) e v,
region_ok ubs0segs E m (YP09.mkRegion (Some 2%nat) flo fhi fwlo fwhi xc) -> bv_unsigned (ew E 2) = sp ->
In (mkChunk off (CVal n e)) xc -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
val_mem ubs0segs m (sp + off) (N.to_nat n) v.
Proof using.
intros E m flo fhi fwlo fwhi xc sp off n e v (_ & _ & _ & Hcs) H2 Hin He Hv Hn. cbn [r_chunks r_base base_val] in Hcs. rewrite H2 in Hcs.
eapply (val_of_chunk_ok ubs0segs); [eapply (proj1 (Forall_forall _ _) Hcs); exact Hin | exact He | exact Hv | exact Hn].
Qed.
Lemma fbC_of_region : forall E m flo fhi fwlo fwhi xc cx cur k7 k46, fields_ok cx cur ->
region_ok ubs0segs E m (YP09.mkRegion (Some 2%nat) flo fhi fwlo fwhi xc) -> bv_unsigned (ew E 2) = c_sp cx -> incl (chC k7 k46) xc ->
ew E 35 = Z_to_bv 64 (c_w cx) -> ew E 36 = Z_to_bv 64 (c_h cx) -> ew E 37 = Z_to_bv 64 (c_top cx) -> ew E 38 = Z_to_bv 64 (c_left cx) ->
ew E k7 = Z_to_bv 64 (ra_iclen cx - 1) -> 0 <= ra_iclen cx - 1 < 256 -> ew E k46 = Z_to_bv 64 (ra_packed cx) -> 0 <= ra_packed cx < 256 ->
fbC m cx.
Proof using.
intros E m flo fhi fwlo fwhi xc cx cur k7 k46 HF HR H2 Hincl H35 H36 H37 H38 Hk7 R7 Hk46 R46.
pose proof HF as (_ & _ & _ & Fw & Fh & Ftop & Fleft & _).
assert (IN : forall c, In c (chC k7 k46) -> In c xc) by (intros c Hc; apply Hincl; exact Hc).
unfold fbC, fb7, fb37, fb46. repeat split.
- eapply (fb_of_region E m flo fhi fwlo fwhi xc (c_sp cx) 7 1 _ _ HR H2 (IN (ch7 k7) ltac:(cbn; tauto))); [cbn [sv_denot]; rewrite Hk7, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia].
- eapply (fb_of_region E m flo fhi fwlo fwhi xc (c_sp cx) 37 1 _ _ HR H2 (IN ch37 ltac:(cbn; tauto))); [reflexivity | cbn; lia | cbn; lia].
- eapply (fb_of_region E m flo fhi fwlo fwhi xc (c_sp cx) 38 2 _ _ HR H2 (IN (mkChunk 38 (CVal 2 (SOff 38 0))) ltac:(cbn; tauto))); [cbn [sv_denot]; rewrite H38, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia].
- eapply (fb_of_region E m flo fhi fwlo fwhi xc (c_sp cx) 40 2 _ _ HR H2 (IN (mkChunk 40 (CVal 2 (SOff 37 0))) ltac:(cbn; tauto))); [cbn [sv_denot]; rewrite H37, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia].
- eapply (fb_of_region E m flo fhi fwlo fwhi xc (c_sp cx) 42 2 _ _ HR H2 (IN (mkChunk 42 (CVal 2 (SOff 35 0))) ltac:(cbn; tauto))); [cbn [sv_denot]; rewrite H35, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia].
- eapply (fb_of_region E m flo fhi fwlo fwhi xc (c_sp cx) 44 2 _ _ HR H2 (IN (mkChunk 44 (CVal 2 (SOff 36 0))) ltac:(cbn; tauto))); [cbn [sv_denot]; rewrite H36, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia].
- eapply (fb_of_region E m flo fhi fwlo fwhi xc (c_sp cx) 46 1 _ _ HR H2 (IN (ch46 k46) ltac:(cbn; tauto))); [cbn [sv_denot]; rewrite Hk46, unsigned_lit_small, Z.add_0_r by lia; reflexivity | cbn; lia | cbn; lia].
Qed.
Lemma fbC_hdr : forall mem cx cur, fields_ok cx cur -> 0 <= ra_packed cx < 256 -> fbC mem cx -> garr8 ubs0segs mem (c_sp cx + 37) (ra_hdr cx).
Proof using.
intros mem cx cur HF R46 (_ & B & C & D & E & F & G). pose proof HF as (_ & _ & _ & Fw & Fh & Ftop & Fleft & _).
assert (T2 : forall a v, 0 <= v < 65536 -> val_mem ubs0segs mem a 2 v -> garr8 ubs0segs mem a (YO07.u16le v)).
{ intros a v Hv H j Hj. unfold YO07.u16le in *. cbn [length] in Hj.
destruct j as [|[|j]]; [| | cbn in Hj; lia]; cbn [nth].
- split; [| apply Z.mod_pos_bound; lia]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (H 0%nat ltac:(lia)). f_equal. unfold le_byte. cbn [Z.of_nat Z.mul]. rewrite !Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 1)) with 256. rewrite (Z.mod_small v 65536) by lia. rewrite ?Zmod_mod. reflexivity.
- split; [| apply Z.mod_pos_bound; lia]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r.
rewrite (H 1%nat ltac:(lia)). f_equal. unfold le_byte. cbn [Z.of_nat Z.mul]. rewrite !Z.shiftr_0_r.
change (2 ^ (8 * Z.of_nat 2)) with 65536. change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 1) with 8. rewrite (Z.mod_small v 65536) by lia. rewrite ?Zmod_mod.
rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
unfold ra_hdr. apply garr8_app. split.
{ intros j Hj. destruct j; [|cbn in Hj; lia]. cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact B | lia]. }
lazymatch goal with |- garr8 _ _ ?a _ => replace a with (c_sp cx + 38) by (cbn; lia) end.
apply garr8_app. split; [apply T2; [lia | exact C]|]. lazymatch goal with |- garr8 _ _ ?a _ => replace a with (c_sp cx + 40) by (cbn; lia) end.
apply garr8_app. split; [apply T2; [lia | exact D]|]. lazymatch goal with |- garr8 _ _ ?a _ => replace a with (c_sp cx + 42) by (cbn; lia) end.
apply garr8_app. split; [apply T2; [lia | exact E]|]. lazymatch goal with |- garr8 _ _ ?a _ => replace a with (c_sp cx + 44) by (cbn; lia) end.
apply garr8_app. split; [apply T2; [lia | exact F]|]. lazymatch goal with |- garr8 _ _ ?a _ => replace a with (c_sp cx + 46) by (cbn; lia) end.
intros j Hj. destruct j; [|cbn in Hj; lia]. cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [exact G | lia].
Qed.
Lemma garr8_cons_val1 : forall m a v l, val_mem ubs0segs m a 1 v -> 0 <= v < 256 -> garr8 ubs0segs m (a + 1) l -> garr8 ubs0segs m a (v :: l).
Proof using.
intros m a v l Hv Rv Hl j Hj. destruct j as [|j].
- cbn [nth Z.of_nat]. rewrite Z.add_0_r. split; [| lia]. intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. pose proof (Hv 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite X.
first [reflexivity | f_equal; f_equal; unfold le_byte; change (8 * Z.of_nat 0) with 0; change (2 ^ (8 * Z.of_nat 1)) with 256; rewrite !Z.shiftr_0_r; rewrite (Z.mod_small v 256) by lia; reflexivity].
- cbn [nth]. cbn [length] in Hj. specialize (Hl j ltac:(lia)). replace (a + Z.of_nat (Datatypes.S j)) with (a + 1 + Z.of_nat j) by lia. exact Hl.
Qed.
Lemma garr8_cons_val2 : forall m a v l, val_mem ubs0segs m a 2 v -> 0 <= v < 65536 -> garr8 ubs0segs m (a + 2) l -> garr8 ubs0segs m a (v mod 256 :: (v / 256) mod 256 :: l).
Proof using.
intros m a v l Hv Rv Hl. apply garr8_cons_val1; [| apply Z.mod_pos_bound; lia | apply garr8_cons_val1; [| apply Z.mod_pos_bound; lia | replace (a + 1 + 1) with (a + 2) by lia; exact Hl]].
- intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. pose proof (Hv 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X. rewrite X. f_equal. f_equal. unfold le_byte.
change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with 65536. rewrite !Z.shiftr_0_r, (Z.mod_small v 65536) by lia. rewrite ?Zmod_mod. reflexivity.
- intros k Hk. destruct k; [|lia]. cbn [Z.of_nat]. rewrite Z.add_0_r. pose proof (Hv 1%nat ltac:(lia)) as X. change (Z.of_nat 1) with 1 in X. rewrite X. f_equal. f_equal. unfold le_byte.
change (8 * Z.of_nat 0) with 0. change (8 * Z.of_nat 1) with 8. change (2 ^ (8 * Z.of_nat 1)) with 256. change (2 ^ (8 * Z.of_nat 2)) with 65536.
rewrite !Z.shiftr_0_r, (Z.mod_small v 65536), Z.shiftr_div_pow2 by lia. rewrite ?Zmod_mod. reflexivity.
Qed.
Lemma gce_garr8 : forall m a d27 dl t30,
val_mem ubs0segs m a 2 63777 -> val_mem ubs0segs m (a + 2) 1 4 -> val_mem ubs0segs m (a + 3) 1 d27 -> 0 <= d27 < 256 ->
val_mem ubs0segs m (a + 4) 2 dl -> 0 <= dl < 65536 -> val_mem ubs0segs m (a + 6) 1 t30 -> 0 <= t30 < 256 -> val_mem ubs0segs m (a + 7) 1 0 ->
garr8 ubs0segs m a ([33; 249; 4; d27] ++ YO07.u16le dl ++ [t30; 0]).
Proof using.
intros m a d27 dl t30 V24 V26 V27 R27 V28 R28 V30 R30 V31. cbn [app YO07.u16le].
change 33 with (63777 mod 256) at 1. change 249 with ((63777 / 256) mod 256) at 1.
apply garr8_cons_val2; [exact V24 | lia |]. apply garr8_cons_val1; [exact V26 | lia |]. replace (a + 2 + 1) with (a + 3) by lia. apply garr8_cons_val1; [exact V27 | lia |]. replace (a + 3 + 1) with (a + 4) by lia.
apply garr8_cons_val2; [exact V28 | lia |]. replace (a + 4 + 2) with (a + 6) by lia. apply garr8_cons_val1; [exact V30 | lia |]. replace (a + 6 + 1) with (a + 7) by lia.
apply garr8_cons_val1; [exact V31 | lia |]. apply garr8_nil.
Qed.
Lemma U_sext16_mod : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 65536 -> bv_unsigned (sv_denot E (SExt true 16 (SOff n 0))) mod 2 ^ (8 * Z.of_N 2) = v.
Proof using.
intros E n v Hn Hv. change (U E (SExt true 16 (SOff n 0)) mod 2 ^ 16 = v).
rewrite U_SExt, (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 16) with 65536. rewrite (Z.mod_small v 65536) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 16) with 65536. change (65536 / 2) with 32768.
unfold zcanon, M64. change (2 ^ 16) with 65536.
destruct (Z.lt_ge_cases v 32768) as [Hlo | Hhi].
- rewrite (Z.mod_small (v + 32768) 65536) by lia. replace (v + 32768 - 32768) with v by lia. rewrite (Z.mod_small v (2 ^ 64)) by lia. apply Z.mod_small. lia.
- replace ((v + 32768) mod 65536) with (v - 32768) by (apply Z.mod_unique_pos with (q := 1); lia).
replace (v - 32768 - 32768) with (v - 65536) by lia.
replace ((v - 65536) mod 2 ^ 64) with (2 ^ 64 + (v - 65536)) by (apply Z.mod_unique_pos with (q := -1); lia).
replace (2 ^ 64 + (v - 65536)) with (v + (2 ^ 48 - 1) * 65536) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma land1_mod2 : forall x, 0 <= x -> Z.land x 1 = x mod 2.
Proof using. intros x Hx. change 1 with (Z.ones 1) at 1. rewrite (Z.land_ones x 1) by lia. reflexivity. Qed.
Lemma U_sext32_par : forall E n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 32 -> Z.land (U E (SExt true 32 (SOff n 0))) 1 = Z.land v 1.
Proof using.
intros E n v Hn Hv. rewrite !land1_mod2 by (first [lia | apply U_range]).
rewrite U_SExt, (U_atom E n v Hn) by lia. change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small v (2 ^ 32)) by lia.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ 32 / 2) with (2 ^ 31).
unfold zcanon, M64.
destruct (Z.lt_ge_cases v (2 ^ 31)) as [Hlo | Hhi].
- rewrite (Z.mod_small (v + 2 ^ 31) (2 ^ 32)) by lia. replace (v + 2 ^ 31 - 2 ^ 31) with v by lia. rewrite (Z.mod_small v (2 ^ 64)) by lia. reflexivity.
- replace ((v + 2 ^ 31) mod 2 ^ 32) with (v - 2 ^ 31) by (apply Z.mod_unique_pos with (q := 1); lia).
replace (v - 2 ^ 31 - 2 ^ 31) with (v - 2 ^ 32) by lia.
replace ((v - 2 ^ 32) mod 2 ^ 64) with (v + (2 ^ 63 - 2 ^ 31) * 2) by (apply Z.mod_unique_pos with (q := -1); lia).
apply Z.mod_add. lia.
Qed.
Lemma gce_test : forall E fattr rattr, ew E 34 = Z_to_bv 64 fattr -> ew E 46 = Z_to_bv 64 rattr -> 0 <= fattr < 2 ^ 32 -> 0 <= rattr < 2 ^ 32 ->
branch_taken BC_NE (sv_denot E (SAlu ALU_AND (SAlu ALU_OR (SExt true 32 (SOff 34 0)) (SExt true 32 (SOff 46 0))) (SLit 1))) (sv_denot E (SLit 0))
= YO07.flag rattr 1 || YO07.flag fattr 1.
Proof using.
intros E fattr rattr H34 H46 Rf Rr. rewrite branch_ne_U, U_and_lit, U_lit by lia.
rewrite U_SAlu. cbn [zalu_raw]. pose proof (U_range E (SExt true 32 (SOff 34 0))) as Ra. pose proof (U_range E (SExt true 32 (SOff 46 0))) as Rb.
unfold M64 in Ra, Rb.
assert (LOR : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= Z.lor a b < 2 ^ 64).
{ intros a b Ha Hb. split; [apply Z.lor_nonneg; lia|].
destruct (Z.eq_dec (Z.lor a b) 0) as [-> | Hnz]; [lia|].
apply Z.log2_lt_pow2; [pose proof (Z.lor_nonneg a b); lia|]. rewrite Z.log2_lor by lia.
apply Z.max_lub_lt; [destruct (Z.eq_dec a 0) as [-> | NE]; [cbn; lia | apply Z.log2_lt_pow2; lia] | destruct (Z.eq_dec b 0) as [-> | NE]; [cbn; lia | apply Z.log2_lt_pow2; lia]]. }
rewrite zcanon_id by (apply LOR; lia). rewrite Z.land_lor_distr_l, (U_sext32_par E 34 fattr H34 Rf), (U_sext32_par E 46 rattr H46 Rr).
unfold YO07.flag. rewrite !land1_mod2 by lia.
pose proof (Z.mod_pos_bound fattr 2 ltac:(lia)). pose proof (Z.mod_pos_bound rattr 2 ltac:(lia)).
assert (C : forall x y, 0 <= x < 2 -> 0 <= y < 2 -> negb (Z.lor x y =? 0) = negb (y =? 0) || negb (x =? 0)).
{ intros x y Hx Hy. assert (x = 0 \/ x = 1) by lia. assert (y = 0 \/ y = 1) by lia. destruct H1 as [-> | ->]; destruct H2 as [-> | ->]; reflexivity. }
apply C; assumption.
Qed.
Lemma test1_sext32 : forall E fattr b, ew E 34 = Z_to_bv 64 fattr -> 0 <= fattr < 2 ^ 32 ->
branch_taken BC_EQ (sv_denot E (SAlu ALU_AND (SExt true 32 (SOff 34 0)) (SLit 1))) (sv_denot E (SLit 0)) = b -> YO07.flag fattr 1 = negb b.
Proof using.
intros E fattr b H34 Rf Hb. rewrite branch_eq_U, U_and_lit, U_lit, (U_sext32_par E 34 fattr H34 Rf) in Hb by lia. unfold YO07.flag. rewrite Hb. reflexivity.
Qed.
Lemma shiftr_mod_byte : forall v m s, 0 <= s -> s + 8 <= m ->
(Z.shiftr (v mod 2 ^ m) s) mod 2 ^ 8 = (Z.shiftr v s) mod 2 ^ 8.
Proof using.
intros v m s Hs Hm. apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 8) as [Hlt|Hge].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia. rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.
Lemma val_of_chunk_ok_mod : forall E mem base off (n : N) (e : sv) v,
chunk_ok ubs0segs E mem base (mkChunk off (CVal n e)) ->
sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> (Z.of_N n <= 8) ->
val_mem ubs0segs mem (base + off) (N.to_nat n) (v mod 2 ^ (8 * Z.of_N n)).
Proof using.
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
Proof using.
intros E a b x y Hx Hy Rx Ry Rp.
rewrite U_of_S, S_SMdw. cbn [zmd_raw]. rewrite Hx, Hy.
rewrite (Z.mod_small x) by lia. rewrite (Z.mod_small y) by lia.
rewrite swrap32_small by lia. apply wrap64_small. lia.
Qed.
Lemma U_mul_small : forall E a b x y, U E a = x -> U E b = y -> 0 <= x -> 0 <= y -> x * y < 2 ^ 64 ->
U E (SMd M_MUL a b) = x * y.
Proof using.
intros E a b x y Hx Hy Rx Ry Rp.
rewrite U_SMd. cbn [zmd_raw]. rewrite Hx, Hy. apply zcanon_id. unfold M64. nia.
Qed.
Lemma U_sll_small : forall E a x k, U E a = x -> 0 <= x -> 0 <= k < 64 -> x * 2 ^ k < 2 ^ 64 ->
U E (SAlu ALU_SLL a (SLit k)) = x * 2 ^ k.
Proof using.
intros E a x k Ha Hx Hk Hxk. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit.
rewrite (zcanon_id k) by (unfold M64; lia).
replace (Z.land k 63) with k.
2:{ change 63 with (Z.ones 6). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. lia. }
rewrite Ha, Z.shiftl_mul_pow2 by lia. apply zcanon_id. unfold M64. nia.
Qed.
Definition hideR (P : Prop) : Prop := P.
Lemma hideR_i : forall P : Prop, P -> hideR P. Proof using. intros P H; exact H. Qed.
Lemma hideR_e : forall P : Prop, hideR P -> P. Proof using. intros P H; exact H. Qed.
Lemma val_mem_mod : forall m a n v, val_mem ubs0segs m a n v <-> val_mem ubs0segs m a n (v mod 2 ^ (8 * Z.of_nat n)).
Proof using.
intros m a n v. unfold val_mem, le_byte.
assert (Hp : 0 < 2 ^ (8 * Z.of_nat n)) by (apply Z.pow_pos_nonneg; lia).
rewrite Z.mod_mod by lia. split; intros H; exact H.
Qed.
Lemma mbyte_eq_of1' : forall (m m' : word -> option byte) a,
m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> mbyte ubs0segs m' a = mbyte ubs0segs m a.
Proof using. intros m m' a H. unfold mbyte. rewrite H. reflexivity. Qed.
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
Ltac pin_regR HS r z Hval :=
lazymatch type of HS with st_ok ?segs ?E1 ?ss1 ?ms1 =>
let H2 := fresh "HSp" in
pose proof (st_ok_pin_regR segs E1 ss1 ms1 r z HS ltac:(first [exact Hval | cbn [ms_regs]; exact Hval | cbn [ms_regs]; rewrite Hval; reflexivity]) eq_refl) as H2;
let v := eval vm_compute in (mkSS (ss_pc ss1) (sr_set (ss_regs ss1) r (SLit z)) (ss_mem ss1) (ss_resv ss1) (ss_facts ss1)) in
change (mkSS (ss_pc ss1) (sr_set (ss_regs ss1) r (SLit z)) (ss_mem ss1) (ss_resv ss1) (ss_facts ss1)) with v in H2;
clear HS; rename H2 into HS
end.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
