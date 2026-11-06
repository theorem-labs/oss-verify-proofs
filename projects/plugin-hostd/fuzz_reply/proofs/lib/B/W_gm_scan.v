(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-30: the ROOM round (an internal work row), A's re-fit git diff f6bfd4d6ab5 f6038f3d481
   of lib/A/W_gm_scan.v applied by three-way merge onto lane W4's ARx text (a working branch 0d0105eaf4d) at
   B's names: pb_gm_scan_x takes the room parameter RP and the three room premises (kr, rp_RM, cnt_ok_pk) and passes
   them to GMFOUND_X and the loop's induction hypothesis. The AR statements (Section r) are W4's, unchanged. *)
(* Modified by Theorem Labs, 2026-10: the IMAGE B (asan-ubsan) scan loop of fuzz_reply's gesture_model, lane W4: the
   frozen cut lib/B/W_gm_cut.v gm_scan_at at the loop head 0x860d8, in the loop form of lib/A/W_gm_scan.v (a fresh
   symbolic state at the head each iteration, built with pa_entry_st_ok_full, run back to the head or on to the found
   point).  Induction on len + j.
   One iteration (B code, fuzz_reply.asan-ubsan.objdump.txt (sha256 17f5c434bf57; internal record)):
     0x860d8 add a6,s2,a0 ; beqz a6 -> 0x861bc   EXIT, NOT TAKEN: decided by the runner from atom 34's fact
                                                 [14, 6000] (a6 = len + j, 13 < len + j, len <= APARTIAL).
     0x860e0 bltu a4,s0 -> unimp 0x8621c         UBSan TRAP (line + len wraps), NOT TAKEN: decided by the runner from
                                                 atom 14's fact [2^64 - 6000, 2^64 - 14] (a4 = -len) and atom 8's
                                                 [4096, 140737479966720] (s0 = LINE; LINE + len <= 140737479966720).
     0x860e4-0x860f8 load1 shadow check of line[len+j-1]; slow path 0x8610c-0x86110, report 0x86114-0x86118
                                                 (__asan_report_load1) NOT TAKEN: the runner's shadow token, with the
                                                 one obligation range_addressable (line[len+j-1]) discharged from the
                                                 line's allocator block (range_addressable_of_block).
     0x860fc lbu a6,-1(a6) ; addi a0,a0,-1 ; bne a6,a3 -> 0x860d8   the byte != ' ': back to the head with j - 1
                                                 (the induction hypothesis; len + j - 1 > 13 because line[13] = ' ').
     0x86108 j 0x8611c                           the byte = ' ': the found point with js = len + j - 1 (GMFOUND).
   Section hypotheses (Section c): lib/B/W_gm_cut.v's header list over a generic allocator relation ARx (LAWS HP0 TL HG
   MTL ABCMP LFIND LPUSH LDROP HLITG HLITB HLITE, the callees at their _x specs) and GMFOUND_X = W_gm_found.v
   pb_gm_found_x's statement verbatim.
   ARx conversion (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record); the template is lib/A/W_gm_scan.v on
   a working branch): Section c proves pb_gm_scan_x (gm_scan_at's statement over ARx); Section r re-derives
   pb_gm_scan, statement unchanged, at ARx := W_journal_x.ARi0 with B's old list (LX0 in place of LAWS, and
   GMFOUND : gm_found_at B MT MMAX G (BASE + A_gm_found), lib/B/W_gm_cut.v:136, frozen). *)
(* Modified by Theorem Labs, 2026-10: the meter and room texts at the KF-COUNT kit's gm_cost H ln (statements only) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep CheckRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_gm_cut.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_shadow_pin.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YCe5x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_journal_x W_sites_x W_contract_x W_kit_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g6.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* The model's side: the last space of the line (lib/Prog/RelayModel.v last_space_from), as lib/A/W_gm_scan.v. *)
Module GMS.
Import RelayModel.
Lemma lsf_none : forall l i, (forall k, (k < length l)%nat -> nth k l 0 <> SPACE) -> last_space_from i l = None.
Proof.
induction l as [|b l IH]; intros i H; [reflexivity|].
cbn [last_space_from]. rewrite IH by (intros k Hk; apply (H (Datatypes.S k)); cbn; lia).
destruct (Z.eqb_spec b SPACE) as [E|E]; [exfalso; apply (H 0%nat); [cbn; lia | exact E] | reflexivity].
Qed.
Lemma lsf : forall l i j, (j < length l)%nat -> nth j l 0 = SPACE ->
(forall k, (j < k < length l)%nat -> nth k l 0 <> SPACE) -> last_space_from i l = Some (i + j)%nat.
Proof.
induction l as [|b l IH]; intros i j Hj HS HN; [cbn in Hj; lia|].
cbn [last_space_from]. destruct j as [|j].
- rewrite lsf_none by (intros k Hk; apply (HN (Datatypes.S k)); cbn; lia).
cbn in HS. rewrite HS. cbn. f_equal. lia.
- rewrite (IH (Datatypes.S i) j) by (cbn in *; first [lia | exact HS | intros k Hk; apply (HN (Datatypes.S k)); lia]).
f_equal. lia.
Qed.
End GMS.

(* The loop's three address sums, as the alias list states them: register n plus a0 (the scan's index, a
   non-positive Z held as a 64-bit wrap) is atom t at offset c (lib/A/W_gm_scan.v u_alias_add). *)
Lemma gms_alias_add : forall E (n t : nat) (v jj c : Z),
ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> ew E 10 = w64 jj ->
ew E t = Z_to_bv 64 (v + jj - c) -> 0 <= v + jj - c < 2 ^ 64 -> 0 <= v + jj < 2 ^ 64 ->
sv_denot E (SAlu ALU_ADD (SOff n 0) (SOff 10 0)) = sv_denot E (SOff t c).
Proof.
intros E n t v jj c Hn Hv H10 Ht Hr Hs.
apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E n v Hn Hv), (U_atom_off E t (v + jj - c) c Ht ltac:(lia) ltac:(lia)).
rewrite U_SOff, H10. unfold w64. rewrite Z_to_bv_unsigned, Z.add_0_r.
unfold zcanon, M64, bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite Zmod_mod, Zplus_mod_idemp_r, Z.mod_small by lia. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).
(* ---- THE GENERIC WALK (route (b), step 3): the scan loop over any allocator relation ARx with its laws.  The Section
   hypotheses beyond the AR walk's: PST / ARx / hl / LAWS (the generic relation) and HP0 (no hidden head in any ARx
   state, a Theorem Labs lane's ruling); the callees are their _x specs at the same PST / ARx, and GMFOUND_X is
   W_gm_found.pb_gm_found_x's statement verbatim. ---- *)
Section c.
Variable B : asyms.
Variable MT : ameter_ops.
(* the room round (W_contract_x.v Section w4): the room parameter, after MT as the kit's spec Sections take it *)
Variable RP : roomp.
Variable MMAX : Z.
Variable G : list (Z * Z).
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes_x SEGS B ARx (SIGMA WS_bcmp).
Hypothesis LFIND : lfind_spec_x B PST ARx G (BASE + AF_fr_list_find).
Hypothesis LPUSH : lp_spec_x B PST ARx MT RP G MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP : ldrop_spec_x B PST ARx MT RP G (BASE + AF_fr_list_drop).
(* the three literals are addressable with a visible shadow hull in every ARx state (W_shadow_pin.v ashp over ARx,
   W_contract_x.ashp_x; at the AR instance W_shadow_pin_fr.v ashp_gesture_13_fr / ashp_begin_5_fr / ashp_end_3_fr). *)
Hypothesis HLITG : ashp_x ARx (VAL A_lit_gesture) 13.
Hypothesis HLITB : ashp_x ARx (VAL A_lit_begin) 5.
Hypothesis HLITE : ashp_x ARx (VAL A_lit_end) 3.
(* The walk from the found point 0x8611c: lib/B/W_gm_found.v pb_gm_found_x, verbatim. *)
Hypothesis GMFOUND_X : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (js : Z) regsc memc mdc,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
cnt_ok_pk RP (gm_pk H) (ablocks B ly S) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
4096 <= LINE -> LINE + Z.of_nat (length ln) <= 140737479966720 -> HA mod 8 = 0 ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
ajournal_gx_x SEGS B PST ARx G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
RelayModel.last_space_from 0 (bzs ln) = Some (Z.to_nat js) ->
13 <= js < Z.of_nat (length ln) ->
getr regsc 10 = w64 (js - Z.of_nat (length ln)) -> getr regsc 11 = w64 (2 ^ 64 - 1 - LINE) ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_found)) memc (seg_rom SEGS)) mdc)
(gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr).

Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Let BR := paj_branch (PI := PI).
(* s3 (x19) holds the shadow base at the loop head: the shadow pattern's Bx is that register's atom. *)
Definition gs_Bx : sv := SOff 19 0.
Definition gs_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* atom 32 = P = line + len + j - 1, the scanned byte's address; 33 = its value; 34 = len + j, the counter *)
Definition gs_extra (P Bv Q : Z) : list word := map (Z_to_bv 64) [P; Bv; Q].
Definition gs_line_region : YP09.region :=
YP09.mkRegion (Some 32%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 33 0))].
Definition gs_regions : smem := [ gs_line_region ].
(* Closed numerals only (the run tactics vm_compute the sstate).  Atom 8 (s0 = LINE) and atom 14 (a4 = -len) decide
   the UBSan wrap trap 0x860e0 `bltu a4, s0`; atom 34 (len + j, which a6 = s2 + a0 aliases) decides the exit
   0x860dc `beqz a6`; the byte's range [0, 255] contains ' ', so the run stops at the back edge `bne a6, a3`.
   a5 + a0 and a2 + a0 are the byte's address and the one after it; the executor's s_alu2 rewrites each sum through
   the alias list to a plain atom offset, which the ASan shadow pattern and the region lookup need. *)
Definition gs_facts : facts :=
mkFacts [ (8%nat, mkAF 4096 140737479966720 0);
(14%nat, mkAF 18446744073709545616 18446744073709551602 0);
(19%nat, mkAF SB SB 0); (32%nat, mkAF 4096 140737479966720 0); (33%nat, mkAF 0 255 0);
(34%nat, mkAF 14 6000 0) ] []
[ (SAlu ALU_ADD (SOff 15 0) (SOff 10 0), SOff 32 0);
  (SAlu ALU_ADD (SOff 12 0) (SOff 10 0), SOff 32 1);
  (SAlu ALU_ADD (SOff 18 0) (SOff 10 0), SOff 34 0) ].
Definition ss_gs : sstate := mkSS A_gm_loop sr_atoms gs_regions None gs_facts.
Definition gs_SH : list shent := [].

Lemma gs_entry : forall (W : world SEGS) (regsc : bvmap 5 word) (memc : word -> option byte) (LINE LEN j P Bv Q : Z),
getr regsc 8 = w64 LINE -> getr regsc 10 = w64 j -> getr regsc 12 = w64 (LINE + LEN) ->
getr regsc 14 = w64 (2 ^ 64 - LEN) -> getr regsc 15 = w64 (LINE + LEN - 1) ->
getr regsc 18 = w64 LEN -> getr regsc 19 = w64 SB ->
P = LINE + LEN - 1 + j -> Q = LEN + j ->
4096 <= LINE -> LINE + LEN <= 140737479966720 -> 14 <= LEN <= 6000 ->
4096 <= P <= 140737479966720 -> 14 <= Q <= 6000 -> 0 <= Bv < 256 ->
val_mem SEGS (mrestrict (w_H W) memc) P 1 Bv ->
st_ok_pi SEGS VAL (Eimg (Ereg regsc (gs_extra P Bv Q))) ss_gs
(restrict (w_H W) (mkst regsc (Z_to_bv 64 (BASE + A_gm_loop)) memc (seg_rom SEGS)))
/\ sh_ok SEGS gs_Bx gs_SH (Eimg (Ereg regsc (gs_extra P Bv Q))) (mrestrict (w_H W) memc).
Proof.
intros W regsc memc LINE LEN j P Bv Q H8 H10 H12 H14 H15 H18 H19 EP EQ RL RLL RN RPa RQ RB VM.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regsc (gs_extra P Bv Q))).
assert (E8 : ew E 8 = getr regsc 8) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 8 8%bv eq_refl)).
assert (E10 : ew E 10 = getr regsc 10) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 10 10%bv eq_refl)).
assert (E12 : ew E 12 = getr regsc 12) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 12 12%bv eq_refl)).
assert (E14 : ew E 14 = getr regsc 14) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 14 14%bv eq_refl)).
assert (E15 : ew E 15 = getr regsc 15) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 15 15%bv eq_refl)).
assert (E18 : ew E 18 = getr regsc 18) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 18 18%bv eq_refl)).
assert (E19 : ew E 19 = getr regsc 19) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 19 19%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 P) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 Bv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 Q) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 2)).
split.
- unfold ss_gs. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold gs_regions, gs_line_region; repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
cbn [base_val]. rewrite E32, unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ P 0 1 (SOff 33 0) Bv);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | zside |].
rewrite Z.add_0_r. exact VM.
+ apply pairwise_disjoint_of_extents. unfold gs_regions, gs_line_region, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. cbn [zpairwise_disjoint zall_disjoint]. repeat split.
+ split; [|split; [exact I|]].
* cbn [gs_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E8, E14, E19, E32, E33, E34, H8, H14, H19. unfold w64.
rewrite !unsigned_lit_small by (unfold SB; lia).
rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end; unfold SB; lia.
* cbn [gs_facts f_alias alias_ok]. split; [|split; [|split; [|exact I]]].
-- apply (gms_alias_add E 15 32 (LINE + LEN - 1) j 0);
[rewrite E15, H15; reflexivity | lia | rewrite E10, H10; reflexivity
| rewrite E32; f_equal; lia | lia | lia].
-- apply (gms_alias_add E 12 32 (LINE + LEN) j 1);
[rewrite E12, H12; reflexivity | lia | rewrite E10, H10; reflexivity
| rewrite E32; f_equal; lia | lia | lia].
-- apply (gms_alias_add E 18 34 LEN j 0);
[rewrite E18, H18; reflexivity | lia | rewrite E10, H10; reflexivity
| rewrite E34; f_equal; lia | lia | lia].
- unfold sh_ok, gs_SH. constructor.
Qed.

(* the loop's region writes nothing: every byte is outside its writable window *)
Ltac gs_outw :=
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); cbn [ss_mem add_cond ss_gs gs_regions In] in Hin;
repeat (destruct Hin as [<- | Hin];
[ cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi gs_line_region] in Hr; lia | ]);
destruct Hin.
(* the view after the runs is the view at the loop head: chain the runs' frames back to memc *)
Ltac gs_meq :=
let a := fresh "a" in let Ha := fresh "Ha" in
intros a Ha;
repeat match goal with
| HFx : frame_of _ _ (mrestrict _ ?m0) (mrestrict _ ?m1) |- aview _ _ ?m1 _ = _ =>
  rewrite (aview_kept_out _ _ _ m0 m1 HFx a Ha) by gs_outw
end; reflexivity.
Ltac gs_in := cbn [In]; repeat first [left; reflexivity | right].
(* x20 .. x27 are in a kept-register list *)
Ltac gs_cs r Hr :=
let Hr8 := fresh "Hr8" in
assert (Hr8 : r = 20 \/ r = 21 \/ r = 22 \/ r = 23 \/ r = 24 \/ r = 25 \/ r = 26 \/ r = 27) by (clear - Hr; lia);
clear - Hr8;
destruct Hr8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; cbn [In];
repeat first [left; apply bv_eq; vm_compute; reflexivity | right].
Ltac gs_spr := unfold GM_STK, GM_FRAME, LP_STK, ASTACK, ASAN_CEIL in *; lia.
Lemma gs_vm : forall (W : world SEGS) (m m' : word -> option byte) a n v,
(forall b, 0 <= b < 2 ^ 64 -> aview SEGS (w_H W) m' b = aview SEGS (w_H W) m b) ->
0 <= a -> a + Z.of_nat n <= 2 ^ 64 -> val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v.
Proof.
intros W m m' a n v Hk H0 H1 Hv. unfold arm in *.
apply (val_mem_kept SEGS (w_H W) (w_H W) m m' a n v); [intros kk Hkk; apply Hk; lia | exact Hv].
Qed.

(* gm_scan_at's statement (lib/B/W_gm_cut.v) over ARx: the AR entry / journal / post at their _x forms. *)
Lemma pb_gm_scan_x : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (j : Z) regsc memc mdc,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
cnt_ok_pk RP (gm_pk H) (ablocks B ly S) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
4096 <= LINE -> LINE + Z.of_nat (length ln) <= 140737479966720 -> HA mod 8 = 0 ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
ajournal_gx_x SEGS B PST ARx G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
getr regsc 10 = w64 j -> getr regsc 11 = w64 (2 ^ 64 - 1 - LINE) ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) -> getr regsc 13 = w64 32 ->
getr regsc 14 = w64 (2 ^ 64 - Z.of_nat (length ln)) ->
getr regsc 15 = w64 (LINE + Z.of_nat (length ln) - 1) ->
14 <= Z.of_nat (length ln) -> 13 < Z.of_nat (length ln) + j -> j <= 0 ->
(forall t, Z.of_nat (length ln) + j <= t < Z.of_nat (length ln) ->
 nth (Z.to_nat t) (bzs ln) 0 <> RelayModel.SPACE) ->
SRr SEGS W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_loop)) memc (seg_rom SEGS)) mdc)
(gm_post_x B PST ARx MT RP G regs ly S Hp W mem md HA H ln kr).
Proof.
intros W ly S hp regs mem md ch HA LINE ln H q k j.
remember (Z.to_nat (Z.of_nat (length ln) + j)) as n eqn:Hn.
revert j Hn.
induction n as [|n IH]; intros j Hn regsc memc mdc
HPRE Hr10 Hr11 Hr12 HL ND HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HAREC HROOM MOK kr HRM HCNT
HFK HSP TLO TLL THA Uspc Cgp Ctp Cs0 Cs1 Cs2 Cs3 CKEPT VRA VS0 VS1 VS2 VS3 KEEPc PRESc HJ
C10 C11 C12 C13 C14 C15 HLEN14 HJ13 HJ0 HINV; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GM_STK = 16528) by reflexivity.
remember (Z.of_nat (length ln)) as LEN eqn:HLEN.
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md q k HAR0 Hq) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _).
assert (Hrq1 : 1 <= req_size k) by lia.
assert (Hrq2 : k <= req_size k)
by (unfold req_size; destruct (k =? 0) eqn:Ek; [apply Z.eqb_eq in Ek | apply Z.eqb_neq in Ek]; lia).
assert (HLO : alloc_ceiling <= spZ regs - GM_STK) by (unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia).
assert (BLK : forall a, q <= a < q + req_size k -> 0 <= a /\ a < spZ regs - GM_STK)
by (intros a Ha; unfold ASAN_CEIL in *; split; lia).
set (idx := LEN + j - 1).
set (Bv := nth (Z.to_nat idx) (bzs ln) 0).
assert (Hidx : 13 <= idx < LEN) by (unfold idx; lia).
assert (Hlnl : Z.of_nat (length (bzs ln)) = LEN) by (unfold bzs; rewrite length_map; lia).
destruct (GL (Z.to_nat idx) ltac:(lia)) as [Hvb Hrb].
assert (HPlo : q <= LINE + idx < q + req_size k) by lia.
destruct (BLK (LINE + idx) HPlo) as [HPl0 HPl1].
assert (VMP : val_mem SEGS (mrestrict (w_H W) memc) (LINE + idx) 1 Bv).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem memc (LINE + idx) 1%nat Bv).
- intros kk Hkk. cbn in Hkk. replace kk with 0 by lia. rewrite Z.add_0_r.
  apply KEEPc; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
- unfold Bv. replace (LINE + idx) with (LINE + Z.of_nat (Z.to_nat idx)) by lia. exact Hvb. }
destruct (gs_entry W regsc memc LINE LEN j (LINE + idx) Bv (LEN + j)
Cs0 C10 C12 C14 C15 Cs2 Cs3 ltac:(unfold idx; lia) ltac:(lia)
TLO TLL ltac:(unfold APARTIAL in *; lia) ltac:(lia) ltac:(unfold APARTIAL in *; lia) Hrb VMP) as [HS SHOK].
remember (Eimg (Ereg regsc (gs_extra (LINE + idx) Bv (LEN + j)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regsc 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = w64 j) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 10 10%bv eq_refl); exact C10).
assert (E13 : ew E 13 = w64 32) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 13 13%bv eq_refl); exact C13).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl); exact Cs3).
assert (E32 : ew E 32 = Z_to_bv 64 (LINE + idx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 Bv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (HAE : env_agree 32 (Ereg regsc (gs_extra (LINE + idx) Bv (LEN + j))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (HBxv : U E gs_Bx = SHADOW_OFF)
by (unfold gs_Bx; rewrite (U_atom E 19 SB E19 ltac:(unfold SB; lia)); reflexivity).
pose proof HJ as HARc. apply ajournal_gx_AR_x in HARc.
(* 0x860d8 .. 0x86104: the exit and the wrap trap decided by the facts, line[len+j-1]'s load1 check (its one
   obligation below), the byte read, j -= 1; the run stops at the back edge `bne a6, a3` *)
paj_run_tok_x RUN HS HJ SHOK gs_Bspan.
{ rewrite <- (aview_rd_of SEGS), HBxv, (U_atom E 32 (LINE + idx) E32 ltac:(lia)).
apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W memc _ q k (LINE + idx) 1 HARc Hq); lia. }
{ apply awr_ok_x_of0. awr_ok_tac. }
assert (F33 : ew (ewset (ewset E 512 w) 513 w0) 33 = Z_to_bv 64 Bv) by (rewrite !ew_ewset_other by lia; exact E33).
assert (F13 : ew (ewset (ewset E 512 w) 513 w0) 13 = Z_to_bv 64 32) by (rewrite !ew_ewset_other by lia; exact E13).
assert (HAE1 : env_agree 32 (Ereg regsc (gs_extra (LINE + idx) Bv (LEN + j))) (ewset (ewset E 512 w) 513 w0)).
{ split; [intros mm Hmm; rewrite !ew_ewset_other by lia; exact (proj1 HAE mm Hmm) | cbn [ewset ed]; exact (proj2 HAE)]. }
assert (Hidx_def : idx = LEN + j - 1) by reflexivity.
assert (HBv : nth (Z.to_nat idx) (bzs ln) 0 = Bv) by reflexivity.
clearbody idx Bv.
psrr_branch_tok RUN BR HS SHOK gs_Bspan.
- (* line[len + j - 1] <> ' ': back to the loop head 0x860d8 with j - 1 *)
  rewrite branch_ne_U, (U_atom _ 33 Bv F33 ltac:(lia)), (U_atom _ 13 32 F13 ltac:(lia)) in Hc.
  apply (proj1 (Bool.negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc.
  (* line[13] is the space, so a byte that is not one sits above it: len + j - 1 > 13 *)
  assert (Hidx14 : 14 <= idx).
  { destruct (Z.eq_dec idx 13) as [I13 | I13]; [|lia]. exfalso. apply Hc. rewrite <- HBv, I13. exact HSP. }
  paj_run_to_tok_x RUNTO HS HJ SHOK gs_Bspan A_gm_loop. { apply awr_ok_x_of0. awr_ok_tac. }
  assert (MEQ0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
  by gs_meq.
  assert (PRES0 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
  { intros a Hp. lazymatch goal with
    | K1 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)),
      K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      exact (apresent_grows _ _ _ a K2 (apresent_grows _ _ _ a K1 (PRESc a Hp))) end. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsc _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 11%bv; 12%bv; 13%bv; 14%bv; 15%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv;
     24%bv; 25%bv; 26%bv; 27%bv] HS HAE1 ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) L10.
  subst LEN.
  pmkst HS.
  apply (IH (j - 1) ltac:(lia) (ms_regs ms0) (ms_mem ms0) _ HPRE Hr10 Hr11 Hr12 HL ND
    HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HAREC HROOM MOK kr HRM HCNT HFK HSP TLO TLL THA).
  + unfold spZ. rewrite (HK 2%bv ltac:(gs_in)). exact Uspc.
  + rewrite (HK 3%bv ltac:(gs_in)). exact Cgp.
  + rewrite (HK 4%bv ltac:(gs_in)). exact Ctp.
  + rewrite (HK 8%bv ltac:(gs_in)). exact Cs0.
  + rewrite (HK 9%bv ltac:(gs_in)). exact Cs1.
  + rewrite (HK 18%bv ltac:(gs_in)). exact Cs2.
  + rewrite (HK 19%bv ltac:(gs_in)). exact Cs3.
  + intros r Hcs Hr. rewrite <- (CKEPT r Hcs Hr). apply HK. gs_cs r Hr.
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VRA].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS0].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS1].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS2].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS3].
  + intros a Ha Hno. rewrite (MEQ0 a Ha). exact (KEEPc a Ha Hno).
  + exact PRES0.
  + exact HJ.
  + rewrite L10, E10. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    rewrite Zplus_mod_idemp_l. f_equal; lia.
  + rewrite (HK 11%bv ltac:(gs_in)). exact C11.
  + rewrite (HK 12%bv ltac:(gs_in)). exact C12.
  + rewrite (HK 13%bv ltac:(gs_in)). exact C13.
  + rewrite (HK 14%bv ltac:(gs_in)). exact C14.
  + rewrite (HK 15%bv ltac:(gs_in)). exact C15.
  + exact HLEN14.
  + lia.
  + lia.
  + intros t Ht. destruct (Z.eq_dec t idx) as [-> | Hne].
    * rewrite HBv. unfold RelayModel.SPACE. exact Hc.
    * apply HINV. lia.
- (* line[len + j - 1] = ' ': `j 0x8611c`, the found point with js = len + j - 1 *)
  rewrite branch_ne_U, (U_atom _ 33 Bv F33 ltac:(lia)), (U_atom _ 13 32 F13 ltac:(lia)) in Hc.
  apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_tok_x RUNTO HS HJ SHOK gs_Bspan A_gm_found. { apply awr_ok_x_of0. awr_ok_tac. }
  assert (MEQ0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
  by gs_meq.
  assert (PRES0 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
  { intros a Hp. lazymatch goal with
    | K1 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)),
      K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      exact (apresent_grows _ _ _ a K2 (apresent_grows _ _ _ a K1 (PRESc a Hp))) end. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsc _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 11%bv; 12%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
     26%bv; 27%bv] HS HAE1 ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) L10.
  subst LEN.
  pmkst HS.
  apply (GMFOUND_X W ly S hp regs mem md ch HA LINE ln H q k idx (ms_regs ms0) (ms_mem ms0) _ HPRE Hr10 Hr11 Hr12 HL ND
    HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HAREC HROOM MOK kr HRM HCNT HFK HSP TLO TLL THA).
  + unfold spZ. rewrite (HK 2%bv ltac:(gs_in)). exact Uspc.
  + rewrite (HK 3%bv ltac:(gs_in)). exact Cgp.
  + rewrite (HK 4%bv ltac:(gs_in)). exact Ctp.
  + rewrite (HK 8%bv ltac:(gs_in)). exact Cs0.
  + rewrite (HK 9%bv ltac:(gs_in)). exact Cs1.
  + rewrite (HK 18%bv ltac:(gs_in)). exact Cs2.
  + rewrite (HK 19%bv ltac:(gs_in)). exact Cs3.
  + intros r Hcs Hr. rewrite <- (CKEPT r Hcs Hr). apply HK. gs_cs r Hr.
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VRA].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS0].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS1].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS2].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS3].
  + intros a Ha Hno. rewrite (MEQ0 a Ha). exact (KEEPc a Ha Hno).
  + exact PRES0.
  + exact HJ.
  + apply (GMS.lsf (bzs ln) 0 (Z.to_nat idx)).
    * lia.
    * rewrite HBv, Hc. reflexivity.
    * intros kk Hkk. replace kk with (Z.to_nat (Z.of_nat kk)) by lia. apply HINV. lia.
  + lia.
  + rewrite L10, E10. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    rewrite Zplus_mod_idemp_l. f_equal; lia.
  + rewrite (HK 11%bv ltac:(gs_in)). exact C11.
  + rewrite (HK 12%bv ltac:(gs_in)). exact C12.
Qed.
(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the scan loop at a world relation R, R a Section variable with its laws R_refl /
   R_trans / WLE_R; the image-B twin of lib/A/W_gm_scan.v's Section wR.  Against the strict texts: ajournal_gx_x SEGS B
   PST ARx -> ajournal_gx_xR SEGS B PST ARx R, SRr SEGS -> SRrG SEGS R, gm_post_x B PST ARx -> gm_post_xR B PST ARx R;
   GMFOUND_XR is GMFOUND_X under these substitutions, the text of W_gm_found.v pb_gm_found_xR, so a composer discharges
   it with that lemma; the runs and the branch are their SRrG forms (W_journal_x.v paj_run_x_xG / paj_run_to_x_xG,
   W_kit.v paj_branch_xR).  The loop calls no allocator function, so the list_push / list_drop contracts are not
   premises here.  The strict pb_gm_scan_x above keeps its proof. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* :136 GMFOUND_X at R *)
Hypothesis GMFOUND_XR : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (js : Z) regsc memc mdc,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
cnt_ok_pk RP (gm_pk H) (ablocks B ly S) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
4096 <= LINE -> LINE + Z.of_nat (length ln) <= 140737479966720 -> HA mod 8 = 0 ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
RelayModel.last_space_from 0 (bzs ln) = Some (Z.to_nat js) ->
13 <= js < Z.of_nat (length ln) ->
getr regsc 10 = w64 (js - Z.of_nat (length ln)) -> getr regsc 11 = w64 (2 ^ 64 - 1 - LINE) ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_found)) memc (seg_rom SEGS)) mdc)
(gm_post_xR B PST ARx R MT RP G regs ly S Hp W mem md HA H ln kr).
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).
(* :297 pb_gm_scan_x *)
Lemma pb_gm_scan_xR : forall W ly S Hp regs mem md ch HA LINE (ln : list byte) H q k (j : Z) regsc memc mdc,
afn_pre_x SEGS B ARx GM_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 HA -> getr regs 11 = w64 LINE -> getr regs 12 = w64 (Z.of_nat (length ln)) ->
alist_at B ly S W mem (HA + 80) H true -> NoDup (texts H) ->
(forall a, HA + 80 <= a < HA + 96 -> inG G a) -> azs B (HA + 80) 16 ->
(HA + 80) mod 8 = 0 ->
garr8 SEGS (arm W mem) LINE (bzs ln) -> ~ In (Z_to_bv 8 0) ln -> Z.of_nat (length ln) <= APARTIAL ->
In (q, k) (ablocks B ly S) -> ~ In (q, k) (list_blks H) -> q <= LINE ->
LINE + Z.of_nat (length ln) <= q + req_size k ->
garr8 SEGS (arm W mem) (VAL A_lit_gesture) RelayModel.K_GESTURE ->
garr8 SEGS (arm W mem) (VAL A_lit_begin) RelayModel.W_BEGIN ->
garr8 SEGS (arm W mem) (VAL A_lit_end) RelayModel.W_END ->
rom_view SEGS W mem ->
(lp_grow H = true -> lp_vbytes H < MMAX) -> AREC * hl_cap H < 2 ^ 32 ->
blocks_bytes S + (if lp_grow H then lp_vbytes H else 0) + (Z.of_nat (length ln) + 1) <= LIVE_MAX ->
mo_ok MT S (gm_cost MT H ln) ->
forall kr : nat,
rp_RM RP S (Z.to_nat (gm_cost MT_rk H ln) + kr) ->
cnt_ok_pk RP (gm_pk H) (ablocks B ly S) ->
firstn 13 (bzs ln) = RelayModel.K_GESTURE ->
nth 13 (bzs ln) 0 = RelayModel.SPACE ->
4096 <= LINE -> LINE + Z.of_nat (length ln) <= 140737479966720 -> HA mod 8 = 0 ->
spZ regsc = spZ regs - GM_FRAME ->
getr regsc 3 = w64 (as_gp B) -> getr regsc 4 = w64 (as_tp B) ->
getr regsc 8 = w64 LINE -> getr regsc 9 = w64 HA ->
getr regsc 18 = w64 (Z.of_nat (length ln)) -> getr regsc 19 = w64 SB ->
(forall r, acallee_saved r -> 20 <= r <= 27 -> getr regsc (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
val_mem SEGS (arm W memc) (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) ->
val_mem SEGS (arm W memc) (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) ->
val_mem SEGS (arm W memc) (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) ->
val_mem SEGS (arm W memc) (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) ->
val_mem SEGS (arm W memc) (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - GM_STK <= a < spZ regs) ->
 aview SEGS (w_H W) memc a = aview SEGS (w_H W) mem a) ->
(forall a, apresent (w_H W) mem a -> apresent (w_H W) memc a) ->
ajournal_gx_xR SEGS B PST ARx R G 0 [] GM_STK (spZ regs) (blk_FP (list_blks H)) ly S Hp W mem md [] ly S Hp W memc mdc 0 ->
getr regsc 10 = w64 j -> getr regsc 11 = w64 (2 ^ 64 - 1 - LINE) ->
getr regsc 12 = w64 (LINE + Z.of_nat (length ln)) -> getr regsc 13 = w64 32 ->
getr regsc 14 = w64 (2 ^ 64 - Z.of_nat (length ln)) ->
getr regsc 15 = w64 (LINE + Z.of_nat (length ln) - 1) ->
14 <= Z.of_nat (length ln) -> 13 < Z.of_nat (length ln) + j -> j <= 0 ->
(forall t, Z.of_nat (length ln) + j <= t < Z.of_nat (length ln) ->
 nth (Z.to_nat t) (bzs ln) 0 <> RelayModel.SPACE) ->
SRrG SEGS R W (mkCfg (mkst regsc (Z_to_bv 64 (BASE + A_gm_loop)) memc (seg_rom SEGS)) mdc)
(gm_post_xR B PST ARx R MT RP G regs ly S Hp W mem md HA H ln kr).
Proof using fx rc SK PI B MT RP MMAX G PST ARx hl LAWS HP0 HG R GMFOUND_XR RUNG RUNTOG BRR.
intros W ly S hp regs mem md ch HA LINE ln H q k j.
remember (Z.to_nat (Z.of_nat (length ln) + j)) as n eqn:Hn.
revert j Hn.
induction n as [|n IH]; intros j Hn regsc memc mdc
HPRE Hr10 Hr11 Hr12 HL ND HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HAREC HROOM MOK kr HRM HCNT
HFK HSP TLO TLL THA Uspc Cgp Ctp Cs0 Cs1 Cs2 Cs3 CKEPT VRA VS0 VS1 VS2 VS3 KEEPc PRESc HJ
C10 C11 C12 C13 C14 C15 HLEN14 HJ13 HJ0 HINV; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HPRE as (HAR0 & Hra & Hra4 & Hgp0 & Htp0 & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (WS : GM_STK = 16528) by reflexivity.
remember (Z.of_nat (length ln)) as LEN eqn:HLEN.
destruct (alx_blocks _ _ _ LAWS ly S hp W mem md q k HAR0 Hq) as (Hq16 & Hq4096 & Hqceil & Hqh_ia & Hqpres & _).
assert (Hrq1 : 1 <= req_size k) by lia.
assert (Hrq2 : k <= req_size k)
by (unfold req_size; destruct (k =? 0) eqn:Ek; [apply Z.eqb_eq in Ek | apply Z.eqb_neq in Ek]; lia).
assert (HLO : alloc_ceiling <= spZ regs - GM_STK) by (unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia).
assert (BLK : forall a, q <= a < q + req_size k -> 0 <= a /\ a < spZ regs - GM_STK)
by (intros a Ha; unfold ASAN_CEIL in *; split; lia).
set (idx := LEN + j - 1).
set (Bv := nth (Z.to_nat idx) (bzs ln) 0).
assert (Hidx : 13 <= idx < LEN) by (unfold idx; lia).
assert (Hlnl : Z.of_nat (length (bzs ln)) = LEN) by (unfold bzs; rewrite length_map; lia).
destruct (GL (Z.to_nat idx) ltac:(lia)) as [Hvb Hrb].
assert (HPlo : q <= LINE + idx < q + req_size k) by lia.
destruct (BLK (LINE + idx) HPlo) as [HPl0 HPl1].
assert (VMP : val_mem SEGS (mrestrict (w_H W) memc) (LINE + idx) 1 Bv).
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem memc (LINE + idx) 1%nat Bv).
- intros kk Hkk. cbn in Hkk. replace kk with 0 by lia. rewrite Z.add_0_r.
  apply KEEPc; unfold GM_STK, GM_FRAME, LP_STK, ASTACK in *; lia.
- unfold Bv. replace (LINE + idx) with (LINE + Z.of_nat (Z.to_nat idx)) by lia. exact Hvb. }
destruct (gs_entry W regsc memc LINE LEN j (LINE + idx) Bv (LEN + j)
Cs0 C10 C12 C14 C15 Cs2 Cs3 ltac:(unfold idx; lia) ltac:(lia)
TLO TLL ltac:(unfold APARTIAL in *; lia) ltac:(lia) ltac:(unfold APARTIAL in *; lia) Hrb VMP) as [HS SHOK].
remember (Eimg (Ereg regsc (gs_extra (LINE + idx) Bv (LEN + j)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (E2 : ew E 2 = getr regsc 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regsc _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = w64 j) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 10 10%bv eq_refl); exact C10).
assert (E13 : ew E 13 = w64 32) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 13 13%bv eq_refl); exact C13).
assert (E19 : ew E 19 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regsc _ 19 19%bv eq_refl); exact Cs3).
assert (E32 : ew E 32 = Z_to_bv 64 (LINE + idx)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 Bv) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regsc _ 1)).
assert (HAE : env_agree 32 (Ereg regsc (gs_extra (LINE + idx) Bv (LEN + j))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (HBxv : U E gs_Bx = SHADOW_OFF)
by (unfold gs_Bx; rewrite (U_atom E 19 SB E19 ltac:(unfold SB; lia)); reflexivity).
pose proof HJ as HARc. apply ajournal_gx_AR_xR in HARc.
(* 0x860d8 .. 0x86104: the exit and the wrap trap decided by the facts, line[len+j-1]'s load1 check (its one
   obligation below), the byte read, j -= 1; the run stops at the back edge `bne a6, a3` *)
paj_run_tok_xR RUNG HS HJ SHOK gs_Bspan.
{ rewrite <- (aview_rd_of SEGS), HBxv, (U_atom E 32 (LINE + idx) E32 ltac:(lia)).
apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly S hp W memc _ q k (LINE + idx) 1 HARc Hq); lia. }
{ apply awr_ok_x_of0. awr_ok_tac. }
assert (F33 : ew (ewset (ewset E 512 w) 513 w0) 33 = Z_to_bv 64 Bv) by (rewrite !ew_ewset_other by lia; exact E33).
assert (F13 : ew (ewset (ewset E 512 w) 513 w0) 13 = Z_to_bv 64 32) by (rewrite !ew_ewset_other by lia; exact E13).
assert (HAE1 : env_agree 32 (Ereg regsc (gs_extra (LINE + idx) Bv (LEN + j))) (ewset (ewset E 512 w) 513 w0)).
{ split; [intros mm Hmm; rewrite !ew_ewset_other by lia; exact (proj1 HAE mm Hmm) | cbn [ewset ed]; exact (proj2 HAE)]. }
assert (Hidx_def : idx = LEN + j - 1) by reflexivity.
assert (HBv : nth (Z.to_nat idx) (bzs ln) 0 = Bv) by reflexivity.
clearbody idx Bv.
psrr_branch_tok RUNG BRR HS SHOK gs_Bspan.
- (* line[len + j - 1] <> ' ': back to the loop head 0x860d8 with j - 1 *)
  rewrite branch_ne_U, (U_atom _ 33 Bv F33 ltac:(lia)), (U_atom _ 13 32 F13 ltac:(lia)) in Hc.
  apply (proj1 (Bool.negb_true_iff _)) in Hc. apply Z.eqb_neq in Hc.
  (* line[13] is the space, so a byte that is not one sits above it: len + j - 1 > 13 *)
  assert (Hidx14 : 14 <= idx).
  { destruct (Z.eq_dec idx 13) as [I13 | I13]; [|lia]. exfalso. apply Hc. rewrite <- HBv, I13. exact HSP. }
  paj_run_to_tok_xR RUNTOG HS HJ SHOK gs_Bspan A_gm_loop. { apply awr_ok_x_of0. awr_ok_tac. }
  assert (MEQ0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
  by gs_meq.
  assert (PRES0 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
  { intros a Hp. lazymatch goal with
    | K1 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)),
      K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      exact (apresent_grows _ _ _ a K2 (apresent_grows _ _ _ a K1 (PRESc a Hp))) end. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsc _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 11%bv; 12%bv; 13%bv; 14%bv; 15%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv;
     24%bv; 25%bv; 26%bv; 27%bv] HS HAE1 ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) L10.
  subst LEN.
  pmkst HS.
  apply (IH (j - 1) ltac:(lia) (ms_regs ms0) (ms_mem ms0) _ HPRE Hr10 Hr11 Hr12 HL ND
    HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HAREC HROOM MOK kr HRM HCNT HFK HSP TLO TLL THA).
  + unfold spZ. rewrite (HK 2%bv ltac:(gs_in)). exact Uspc.
  + rewrite (HK 3%bv ltac:(gs_in)). exact Cgp.
  + rewrite (HK 4%bv ltac:(gs_in)). exact Ctp.
  + rewrite (HK 8%bv ltac:(gs_in)). exact Cs0.
  + rewrite (HK 9%bv ltac:(gs_in)). exact Cs1.
  + rewrite (HK 18%bv ltac:(gs_in)). exact Cs2.
  + rewrite (HK 19%bv ltac:(gs_in)). exact Cs3.
  + intros r Hcs Hr. rewrite <- (CKEPT r Hcs Hr). apply HK. gs_cs r Hr.
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VRA].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS0].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS1].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS2].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS3].
  + intros a Ha Hno. rewrite (MEQ0 a Ha). exact (KEEPc a Ha Hno).
  + exact PRES0.
  + exact HJ.
  + rewrite L10, E10. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    rewrite Zplus_mod_idemp_l. f_equal; lia.
  + rewrite (HK 11%bv ltac:(gs_in)). exact C11.
  + rewrite (HK 12%bv ltac:(gs_in)). exact C12.
  + rewrite (HK 13%bv ltac:(gs_in)). exact C13.
  + rewrite (HK 14%bv ltac:(gs_in)). exact C14.
  + rewrite (HK 15%bv ltac:(gs_in)). exact C15.
  + exact HLEN14.
  + lia.
  + lia.
  + intros t Ht. destruct (Z.eq_dec t idx) as [-> | Hne].
    * rewrite HBv. unfold RelayModel.SPACE. exact Hc.
    * apply HINV. lia.
- (* line[len + j - 1] = ' ': `j 0x8611c`, the found point with js = len + j - 1 *)
  rewrite branch_ne_U, (U_atom _ 33 Bv F33 ltac:(lia)), (U_atom _ 13 32 F13 ltac:(lia)) in Hc.
  apply (proj1 (Bool.negb_false_iff _)) in Hc. apply Z.eqb_eq in Hc.
  paj_run_to_tok_xR RUNTOG HS HJ SHOK gs_Bspan A_gm_found. { apply awr_ok_x_of0. awr_ok_tac. }
  assert (MEQ0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
  by gs_meq.
  assert (PRES0 : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms0) a).
  { intros a Hp. lazymatch goal with
    | K1 : mem_grows (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms)),
      K2 : mem_grows (mrestrict (w_H W) (ms_mem ms)) (mrestrict (w_H W) (ms_mem ms0)) |- _ =>
      exact (apresent_grows _ _ _ a K2 (apresent_grows _ _ _ a K1 (PRESc a Hp))) end. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regsc _
    [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 11%bv; 12%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
     26%bv; 27%bv] HS HAE1 ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (10%bv : bv 5) L10.
  subst LEN.
  pmkst HS.
  apply (GMFOUND_XR W ly S hp regs mem md ch HA LINE ln H q k idx (ms_regs ms0) (ms_mem ms0) _ HPRE Hr10 Hr11 Hr12 HL ND
    HinG HZS HA8 GL NZ LN Hq Hqb Hq1 Hq2 LG LB LE HROM HGROW HAREC HROOM MOK kr HRM HCNT HFK HSP TLO TLL THA).
  + unfold spZ. rewrite (HK 2%bv ltac:(gs_in)). exact Uspc.
  + rewrite (HK 3%bv ltac:(gs_in)). exact Cgp.
  + rewrite (HK 4%bv ltac:(gs_in)). exact Ctp.
  + rewrite (HK 8%bv ltac:(gs_in)). exact Cs0.
  + rewrite (HK 9%bv ltac:(gs_in)). exact Cs1.
  + rewrite (HK 18%bv ltac:(gs_in)). exact Cs2.
  + rewrite (HK 19%bv ltac:(gs_in)). exact Cs3.
  + intros r Hcs Hr. rewrite <- (CKEPT r Hcs Hr). apply HK. gs_cs r Hr.
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VRA].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS0].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS1].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS2].
  + apply (gs_vm W memc _ _ _ _ MEQ0); [gs_spr | gs_spr | exact VS3].
  + intros a Ha Hno. rewrite (MEQ0 a Ha). exact (KEEPc a Ha Hno).
  + exact PRES0.
  + exact HJ.
  + apply (GMS.lsf (bzs ln) 0 (Z.to_nat idx)).
    * lia.
    * rewrite HBv, Hc. reflexivity.
    * intros kk Hkk. replace kk with (Z.to_nat (Z.of_nat kk)) by lia. apply HINV. lia.
  + lia.
  + rewrite L10, E10. unfold w64. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    rewrite Zplus_mod_idemp_l. f_equal; lia.
  + rewrite (HK 11%bv ltac:(gs_in)). exact C11.
  + rewrite (HK 12%bv ltac:(gs_in)). exact C12.
Qed.
End wR.

End c.

(* ---- THE AR STATEMENT, re-derived (route (b), step 3; CONVERSION.md (sha256 1015972e02a9; internal record) 3.-4.): pb_gm_scan's statement is the AR walk's,
   unchanged, now a corollary of pb_gm_scan_x at ARx := ARi0, PST := [].  LX0 replaces LAWS; HP0 at ARi0 is
   ARi0_hp0; the old GMFOUND gives GMFOUND_X at ARi0 (its pre and journal at ARi0 are the AR ones by
   W_journal_x afn_pre_x_ARi0_to_AR / ajournal_gx_x_ARi0_AR, its post the generic one by W_contract_x
   gm_post_x_of_AR0); the entry, the journal and the post through afn_pre_x_ARi0_of_AR / ajournal_gx_AR_x_ARi0 /
   gm_post_x_AR0. ---- *)
Section r.
Variable B : asyms.
Variable MT : ameter_ops.
Variable MMAX : Z.
Variable G : list (Z * Z).
Hypothesis LX0 : AR_laws_x SEGS B (ARi0 SEGS B) 0.
Hypothesis TL : PALib B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMP : abcmp_realizes SEGS B (SIGMA WS_bcmp).
Hypothesis LFIND : lfind_spec B G (BASE + AF_fr_list_find).
Hypothesis LPUSH : lp_spec B MT G MMAX (BASE + AF_fr_list_push).
Hypothesis LDROP : ldrop_spec B MT G (BASE + AF_fr_list_drop).
(* the three literals are addressable with a visible shadow hull in every AR state (W_shadow_pin.v ashp, a theorem of
   AR at the instance: W_shadow_pin_fr.v ashp_gesture_13_fr / ashp_begin_5_fr / ashp_end_3_fr).  The zero-shadow
   claims that stood here were false (partial last granules). *)
Hypothesis HLITG : ashp B (VAL A_lit_gesture) 13.
Hypothesis HLITB : ashp B (VAL A_lit_begin) 5.
Hypothesis HLITE : ashp B (VAL A_lit_end) 3.
(* The walk from the found point 0x8611c: lib/B/W_gm_cut.v gm_found_at (frozen), lane W4's found hand. *)
Hypothesis GMFOUND : gm_found_at B MT MMAX G (BASE + A_gm_found).

(* a premise at ARi0 turned into its AR form (the pre gives Hp = []), then fed to the AR hypothesis; the room round's
   kr, rp_RM and cnt_ok_pk premises have no AR counterpart and are skipped *)
Local Ltac go1 H :=
  lazymatch goal with
  | |- forall _, _ =>
    let x := fresh "x" in intro x;
    lazymatch type of x with
    | nat => idtac
    | context [rp_RM] => idtac
    | context [cnt_ok_pk] => idtac
    | _ =>
      lazymatch type of x with
      | context [@afn_pre_x] =>
        let E := fresh "E" in pose proof (proj2 (proj1 x)) as E; apply afn_pre_x_ARi0_to_AR in x;
        lazymatch type of E with ?v = _ => subst v end
      | context [@ajournal_gx_x] => apply ajournal_gx_x_ARi0_AR in x
      | _ => idtac
      end;
      specialize (H x)
    end; go1 H
  | |- _ => idtac
  end.
Theorem pb_gm_scan : gm_scan_at B MT MMAX G (BASE + A_gm_loop).
Proof.
unfold gm_scan_at.
intros W ly S regs mem md ch HA LINE ln H q k j regsc memc mdc HPRE. intros.
pose proof (ARi0_hp0 SEGS B) as HP0.
pose proof (afn_pre_x_ARi0_of_AR SEGS B _ _ _ _ _ _ _ _ HPRE) as HPREx.
lazymatch goal with HJ : context [@W_journal.ajournal_gx] |- _ =>
  pose proof HJ as HJx; apply ajournal_gx_AR_x_ARi0 with (Hp := []) in HJx end.
eapply SRr_mono.
{ eapply (pb_gm_scan_x B MT RP_AR MMAX G [] (ARi0 SEGS B)) with (kr := 0%nat); try eassumption.
  all: first
    [ exact (rp_RM_AR _ _)
    | apply cnt_ok_pk_AR; unfold gm_pk; cbn; lia
    | intros W1 ly1 S1 Hp1; pose proof GMFOUND as GMF; unfold gm_found_at in GMF; specialize (GMF W1 ly1 S1); go1 GMF;
      eapply SRr_mono; [exact GMF | cbv beta; intros W2 c2 _ HQ; apply gm_post_x_of_AR0; exact HQ] ]. }
cbv beta. intros W2 c2 _ HQ. exact (gm_post_x_AR0 B MT G regs ly S [] W mem md HA H ln _ W2 c2 HQ).
Qed.
End r.
End b.
End a.
