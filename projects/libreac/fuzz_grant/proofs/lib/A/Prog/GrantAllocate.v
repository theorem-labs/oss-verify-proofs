(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the contract and walk of reac_grant_allocate on fuzz_grant.asan, written for libreac/fuzz_grant with proof steps adapted from proofs/cgif/cgif_file_fuzzer/lib/A/AChd.v. *)
(* reac_grant_allocate (0x84860) on fuzz_grant's ASan build: the call admits a
   box's announced base and width and writes the two bytes of the caller's
   struct reac_grant_alloc (base, width). The harness keeps that struct in the
   side-stack frame of the target's entry function, so the two bytes belong to
   the caller and the contract is in cgif's caller-journal form
   (proofs/cgif/cgif_file_fuzzer/lib/YC20.v:311-365): the premise is the caller's
   journal, the right to write the two bytes is a premise the caller supplies
   per byte, and the post extends the same journal.

   The admission rule is GrantModel.fits, Pau's address-free model; the overflow
   premise is hers too (lib/Prog/reac_grant_allocate_c.v:16), because the C adds
   base + width as int.  tcj_kept and twr_ok come from CtrlFinish.v, which holds
   this slice's shared shapes. *)
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI16.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Reusable Require Import YM05 YO0a YO0b YO0c.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import
PaTable PaSym PaShadow PaStep PaRun PaJournal GrantSyms GrantList GrantAddr GrantPa GrantPaLib GrantBase CtrlFinish.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.A.Prog Require Import GrantAllocFits.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.
Ltac zbool_a :=
repeat match goal with
| H : negb _ = true |- _ => apply Bool.negb_true_iff in H
| H : negb _ = false |- _ => apply Bool.negb_false_iff in H
| H : (_ =? _) = true |- _ => apply Z.eqb_eq in H
| H : (_ =? _) = false |- _ => apply Z.eqb_neq in H
| H : (_ <? _) = true |- _ => apply Z.ltb_lt in H
| H : (_ <? _) = false |- _ => apply Z.ltb_ge in H
| H : (_ <=? _) = true |- _ => apply Z.leb_le in H
| H : (_ <=? _) = false |- _ => apply Z.leb_gt in H
| H : (_ && _) = true |- _ => apply andb_prop in H; destruct H
| H : (_ && _) = false |- _ => apply Bool.andb_false_iff in H; destruct H
end.
Ltac unwrap_a :=
unfold bv_swrap, bv_wrap, zcanon, M64 in *;
try change (bv_modulus 64) with (2 ^ 64) in *; try change (bv_modulus 32) with (2 ^ 32) in *;
try change (bv_half_modulus 64) with (2 ^ 63) in *; try change (bv_half_modulus 32) with (2 ^ 31) in *.
Ltac fits_val := unfold fits;
repeat match goal with |- context [?a <=? ?b] => destruct (Z.leb_spec a b) end;
cbn [andb]; first [reflexivity | exfalso; lia].
Ltac lits_a :=
change (2 ^ 64) with 18446744073709551616 in *; change (2 ^ 32) with 4294967296 in *;
change (2 ^ 31) with 2147483648 in *; change (2 ^ 63) with 9223372036854775808 in *.
Ltac ifs_lia_a := repeat match goal with |- context [if ?c then _ else _] => destruct c eqn:? end; zbool_a; lia.
Ltac bool_lia_a :=
repeat match goal with
| |- (_ <? _) = true => apply Z.ltb_lt
| |- (_ <? _) = false => apply Z.ltb_ge
| |- (_ <=? _) = true => apply Z.leb_le
| |- (_ <=? _) = false => apply Z.leb_gt
end; zbool_a; lia.
Lemma cond_bw : forall E x, ew E 12 = Z_to_bv 64 x -> int32 x ->
branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 12 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551576)) = negb ((1 <=? x) && (x <=? 40)).
Proof.
intros E x H Hx. unfold int32 in Hx.
assert (Q : (if branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 12 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551576)) then 1 else 0)
= (if (1 <=? x) && (x <=? 40) then 0 else 1)).
{ rewrite branch_ltu_U. unfold U. cbn [sv_denot].
rewrite addw_rr_unsigned, H, Z.add_0_r, !Z_to_bv_unsigned. unwrap_a. lits_a.
rewrite (Z.mod_mod x 18446744073709551616) by lia.
rewrite (addw_congr (x mod 18446744073709551616) x (-41 mod 18446744073709551616) (-41))
by (change (2 ^ 32) with 4294967296; apply mod64_mod32).
replace (18446744073709551576 mod 18446744073709551616) with 18446744073709551576 by reflexivity.
unfold addw.
destruct (Z.leb_spec 1 x) as [Ha|Ha]; destruct (Z.leb_spec x 40) as [Hb|Hb]; cbn [andb].
- replace (x + -41) with (- (41 - x)) by lia. rewrite sx32_neg_small by (lits_a; lia). lits_a. ifs_lia_a.
- rewrite sx32_small by (lits_a; lia). ifs_lia_a.
- destruct (Z.leb_spec (41 - 2147483648) x) as [Hc|Hc].
+ replace (x + -41) with (- (41 - x)) by lia. rewrite sx32_neg_small by (lits_a; lia). lits_a. ifs_lia_a.
+ rewrite (sx32_congr (x + -41) (x + -41 + 4294967296))
by (change (2 ^ 32) with 4294967296; symmetry;
replace (x + -41 + 4294967296) with ((x + -41) + 1 * 4294967296) by lia; apply Z.mod_add; lia).
rewrite sx32_small by (lits_a; lia). ifs_lia_a.
- exfalso. lia. }
destruct (branch_taken BC_LTU (sv_denot E (SAluw ALU_ADD (SOff 12 0) (SLit (-41)))) (sv_denot E (SLit 18446744073709551576)));
destruct ((1 <=? x) && (x <=? 40)); cbn in Q |- *; first [reflexivity | discriminate Q].
Qed.
Lemma cond_bb : forall E b, ew E 11 = Z_to_bv 64 b -> int32 b ->
branch_taken BC_LT (sv_denot E (SOff 11 0)) (sv_denot E (SLit 0)) = (b <? 0).
Proof.
intros E b H Hb. unfold int32 in Hb. cbn [branch_taken]. unfold c_lts, bv_lts. cbn [sv_denot].
rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned, (signed64_small b) by lia.
rewrite (signed64_small 0) by lia. reflexivity.
Qed.
Lemma cond_bs : forall E b x, ew E 11 = Z_to_bv 64 b -> ew E 12 = Z_to_bv 64 x ->
0 <= b < 2 ^ 31 -> 1 <= x <= 40 -> b + x < 2 ^ 31 ->
branch_taken BC_LT (sv_denot E (SLit 48)) (sv_denot E (SAluw ALU_ADD (SOff 12 0) (SOff 11 0))) = negb (b + x <=? 48).
Proof.
intros E b x H11 H12 Hb Hx Hs.
assert (Q : (if branch_taken BC_LT (sv_denot E (SLit 48)) (sv_denot E (SAluw ALU_ADD (SOff 12 0) (SOff 11 0))) then 1 else 0)
= (if b + x <=? 48 then 0 else 1)).
{ cbn [branch_taken]. unfold c_lts, bv_lts. cbn [sv_denot].
unfold bv_signed. rewrite addw_rr_unsigned, H11, H12, !Z.add_0_r, !Z_to_bv_unsigned.
unwrap_a. lits_a.
rewrite (Z.mod_mod x 18446744073709551616) by lia.
rewrite (Z.mod_mod b 18446744073709551616) by lia.
rewrite (addw_congr (x mod 18446744073709551616) x (b mod 18446744073709551616) b)
by (change (2 ^ 32) with 4294967296; apply mod64_mod32).
unfold addw. rewrite sx32_small by (lits_a; lia).
replace (48 mod 18446744073709551616) with 48 by reflexivity.
rewrite (Z.mod_small (48 + 9223372036854775808) 18446744073709551616) by lia.
rewrite (Z.mod_small (x + b + 9223372036854775808) 18446744073709551616) by lia.
ifs_lia_a. }
destruct (branch_taken BC_LT (sv_denot E (SLit 48)) (sv_denot E (SAluw ALU_ADD (SOff 12 0) (SOff 11 0))));
destruct (b + x <=? 48); cbn in Q |- *; first [reflexivity | discriminate Q].
Qed.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg grant_listing}.
#[local] Notation SEGS := (@pa_segs _ grant_listing PI).
#[local] Notation VAL := (@pa_val _ grant_listing PI).
#[local] Notation BASE := (@pa_val _ grant_listing PI A_TEXT).
(* Its own frame is 16 bytes; it calls nothing but the error path, and ESTACK is
   what the memory-checking runtime uses below sp. *)
Definition TALLOC_STK : Z := 16 + ESTACK.
Definition EV_ALLOC : Z := 0.
Lemma val_mem1_of_chunk : forall (Ez : env) (m : word -> option byte) (q off : Z) (e : sv) (z : Z),
YP09.chunk_ok SEGS Ez m q (YP09.mkChunk off (CVal 1 e)) -> sv_denot Ez e = Z_to_bv 64 z ->
YI04.val_mem SEGS m (q + off) 1%nat (z mod 256).
Proof.
intros Ez m q off e z Hc Hz kk Hk.
assert (Hk0 : kk = 0%nat) by lia. subst kk.
destruct (Hc 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2).
cbn [YP09.cbyte YP09.c_off YP09.c_val] in Hb1, Hb2. injection Hb1 as <-.
rewrite !Z.add_0_r in Hb2. cbn [Z.of_nat]. rewrite Z.add_0_r. rewrite Hb2. f_equal.
unfold YP09.byte_of_word, le_byte. rewrite Hz, Z_to_bv_unsigned.
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. change (bv_modulus 64) with (2 ^ 64).
change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. change (2 ^ 8) with 256.
rewrite !Z.shiftr_0_r.
unfold YO0f.le_byte. change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0.
change (2 ^ 8) with 256. rewrite Z.shiftr_0_r. rewrite !Z.mod_mod by lia.
symmetry. apply Zmod_div_mod; [lia | lia | exists (2 ^ 56); reflexivity].
Qed.
Lemma aview_of_eq : forall (H : word -> bool) (m m' : word -> option byte) a,
mrestrict H m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) ->
aview SEGS H m' a = aview SEGS H m a.
Proof. intros H m m' a Hq. unfold aview, YP09.mbyte. rewrite Hq. reflexivity. Qed.
Lemma garr8_two : forall (Ez : env) (m : word -> option byte) (q a c : Z) (ea ec : sv),
YP09.chunk_ok SEGS Ez m q (YP09.mkChunk 0 (CVal 1 ea)) ->
YP09.chunk_ok SEGS Ez m q (YP09.mkChunk 1 (CVal 1 ec)) ->
sv_denot Ez ea = Z_to_bv 64 a -> sv_denot Ez ec = Z_to_bv 64 c ->
garr8 SEGS m q [a mod 256; c mod 256].
Proof.
intros Ez m q a c ea ec H0 H1 Ha Hc j Hj.
cbn [length] in Hj.
destruct j as [|j]; [|destruct j as [|j]; [|cbn in Hj; lia]].
- cbn [nth]. split; [|pose proof (Z.mod_pos_bound a 256 ltac:(lia)); lia].
  cbn [Z.of_nat]. rewrite Z.add_0_r.
  pose proof (val_mem1_of_chunk Ez m q 0 ea a H0 Ha) as Hv. rewrite Z.add_0_r in Hv. exact Hv.
- cbn [nth]. split; [|pose proof (Z.mod_pos_bound c 256 ltac:(lia)); lia].
  cbn [Z.of_nat]. exact (val_mem1_of_chunk Ez m q 1 ec c H1 Hc).
Qed.
Section e.
Variable B : asyms.
Definition talloc_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
(lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
(regs : bvmap 5 word) (p base in_ch v0 v1 : Z) : world SEGS -> config -> Prop :=
fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W2 mem2 md2 (k + EV_ALLOC) /\
aregs_preserved regs regs2 /\
getr regs2 10 = w64 (if fits base in_ch then 0 else -1) /\
garr8 SEGS (mrestrict (w_H W2) mem2) p
(if fits base in_ch then [base mod 256; in_ch mod 256] else [v0; v1]) /\
tcj_kept B TALLOC_STK lyc Sc W memc W2 mem2 (spZ regs) (fun a => p <= a < p + 2).
Definition talloc_spec (a : Z) : Prop :=
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p base in_ch v0 v1 : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 10 = w64 p -> getr regs 11 = w64 base -> getr regs 12 = w64 in_ch ->
int32 base -> int32 in_ch ->
(* the C adds base + width as int; the caller rules the overflow out *)
(0 <= base -> 1 <= in_ch <= 40 -> base + in_ch <= 2 ^ 31 - 1) ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TALLOC_STK -> spZ regs <= sp0 ->
(* the caller's two bytes, and what they hold now *)
p + 2 <= 2 ^ 47 - 8 -> (spZ regs <= p \/ p + 2 <= spZ regs - TALLOC_STK) ->
off_img p 2 -> (forall x, p <= x < p + 2 -> app_addr x) ->
twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 2 ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 2 ->
garr8 SEGS (mrestrict (w_H W) memc) p [v0; v1] ->
SRr SEGS W (cfg_at SEGS a regs memc mdc)
(talloc_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs p base in_ch v0 v1).
(* ---- the walk ------------------------------------------------------------ *)
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_grant) (PI := PI).
Definition Bxa : sv := SOff 32 0.
Definition alloc_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
Definition alloc_out : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 2 0 2 [YP09.mkChunk 0 (CVal 1 (SOff 33 0)); YP09.mkChunk 1 (CVal 1 (SOff 34 0))].
Definition alloc_regions : smem := [ stack_region 16; got_regionP; bcell_regionP 32; alloc_out ].
Definition alloc_facts : facts :=
mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 4); (10%nat, mkAF 4096 (2 ^ 47 - 8) 0);
(32%nat, mkAF SB SB 0); (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0) ] [] [].
Definition ss_alloc : sstate := mkSS AF_reac_grant_allocate sr_atoms alloc_regions None alloc_facts.
Definition alloc_SH : list shent := [ mkSHE 10 0 2 ].
Definition alloc_extra (v0 v1 : Z) : list word := map (Z_to_bv 64) [SB; v0; v1].
Definition EA (regs : bvmap 5 word) (v0 v1 : Z) : env := Eimg (Ereg regs (alloc_extra v0 v1)).
Lemma alloc_entry :
forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p v0 v1 : Z),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
getr regs 10 = w64 p ->
spZ regs mod 16 = 0 -> sp0 - STK <= spZ regs - TALLOC_STK -> spZ regs <= sp0 ->
p + 2 <= 2 ^ 47 - 8 -> (spZ regs <= p \/ p + 2 <= spZ regs - TALLOC_STK) ->
off_img p 2 -> (forall x, p <= x < p + 2 -> app_addr x) ->
(forall a, p <= a < p + 2 -> apresent (w_H W) memc a) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF p 2 ->
garr8 SEGS (mrestrict (w_H W) memc) p [v0; v1] ->
st_ok_pi SEGS VAL (EA regs v0 v1) ss_alloc
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_reac_grant_allocate)) memc (seg_rom SEGS)))
/\ sh_ok SEGS Bxa alloc_SH (EA regs v0 v1) (mrestrict (w_H W) memc).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p v0 v1
HJ H10 Hal16 Hwlo Hwhi Hphi Hpside Hoff Happ Hppr HRA HG01.
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : TALLOC_STK = 4112) by reflexivity.
assert (Hsp46 : 2 ^ 46 <= spZ regs <= 2 ^ 47) by lia.
pose proof (app_addr_below_ceil p (Happ p ltac:(lia))) as Hp0.
destruct (al_const _ _ LAWS lyc Sc W memc mdc HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
pose proof (pa_obj_img 32%nat ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD.
pose proof (pa_obj_img 1%nat ltac:(lia)) as HgotR.
pose proof pa_B_ok as HBASE.
destruct (HG01 0%nat ltac:(cbn; lia)) as [Mv0 Rv0]. cbn [nth] in Mv0, Rv0.
destruct (HG01 1%nat ltac:(cbn; lia)) as [Mv1 Rv1]. cbn [nth] in Mv1, Rv1.
cbn [Z.of_nat] in Mv0, Mv1. rewrite Z.add_0_r in Mv0.
rewrite restrict_mkst_fx.
set (E := EA regs v0 v1).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (alloc_extra v0 v1)) n)
by (intros n Hn; subst E; unfold EA; apply Eimg_low; exact Hn).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 v0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 v1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E1g : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E32g : ew E (A_OBJ 32) = Z_to_bv 64 (VAL (A_OBJ 32))) by (subst E; unfold EA; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> base_val E (Some n) = v).
{ intros n v Hn Hv. cbn [base_val]. rewrite Hn. apply unsigned_lit_small. exact Hv. }
assert (Hpg1 : p + 2 <= VAL (A_OBJ 1) \/ VAL (A_OBJ 1) + 8 <= p) by (unfold off_img in Hoff; lia).
assert (Hpg32 : p + 2 <= VAL (A_OBJ 32) \/ VAL (A_OBJ 32) + 8 <= p) by (unfold off_img in Hoff; lia).
split.
- unfold ss_alloc. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold alloc_regions, alloc_out, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. lia.
* rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g) by (pose proof (pa_val_range (A_OBJ 1)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 32) 0) (VAL (A_OBJ 32)));
[cbn [sv_denot]; rewrite E32g, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
| pose proof (pa_val_range (A_OBJ 32)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
* rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E32g) by (pose proof (pa_val_range (A_OBJ 32)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 32)) 0 8 Bxa SB);
[cbn [sv_denot Bxa]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
* rewrite (VB 10%nat p E10) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (apresent_writable SEGS); apply Hppr; lia|].
constructor; [|constructor; [|constructor]].
-- apply (chunk_ok_val SEGS E _ p 0 1 (SOff 33 0) v0);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Mv0.
-- apply (chunk_ok_val SEGS E _ p 1 1 (SOff 34 0) v1);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside | exact Mv1].
+ apply pairwise_disjoint_of_extents.
unfold alloc_regions, alloc_out, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 10%nat p E10) by lia.
rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E1g) by (pose proof (pa_val_range (A_OBJ 1)); lia).
rewrite (VB (A_OBJ 32) (VAL (A_OBJ 32)) E32g) by (pose proof (pa_val_range (A_OBJ 32)); lia).
cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil Hsp46 HcellR HgcD HgotR Hpg1 Hpg32 Hp0 Hphi Hpside C1 C3 WS Hstk0. clear. intros.
repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [alloc_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hsp46 Hal16 Hp0 Hphi Rv0 Rv1. clear. unfold SB. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, alloc_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) memc E Bxa 10%nat p 2 p 0 2 HRA).
+ unfold U, Bxa. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. change (Z.min 0 2) with 0 in Hx. change (Z.max 0 2) with 2 in Hx.
pose proof (Happ x ltac:(lia)) as Hax. unfold app_addr in Hax.
unfold SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
Qed.
Ltac awr_alloc sp0v spv pv Usp E10 HpW :=
lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk sp0 fp b0 bc ly own) end;
eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spv - sp0v));
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite Usp; lia
| cbn; lia | cbn; lia | ];
apply awr_ok_cons_ro; [cbn; lia|];
apply awr_ok_cons_ro; [cbn; lia|];
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 10%nat pv);
[ reflexivity
| cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E10; apply unsigned_lit_small; lia
| cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; exact (proj1 (HpW aa ltac:(lia)))
| apply awr_ok_nil ].
Theorem pb_grant_allocate : talloc_spec (BASE + AF_reac_grant_allocate).
Proof.
unfold talloc_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p base in_ch v0 v1
HJ Hra Hra4 Hgp Htp H10 H11 H12 Hb32 Hc32 Hovf Hal16 Hwlo Hwhi Hphi Hpside Hoff Happ HpW HRA HG01.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
assert (WS : TALLOC_STK = 4112) by reflexivity.
assert (Hppr : forall a, p <= a < p + 2 -> apresent (w_H W) memc a)
by (intros a Ha; exact (proj1 (proj2 (HpW a Ha)))).
destruct (alloc_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p v0 v1
HJ H10 Hal16 Hwlo Hwhi Hphi Hpside Hoff Happ Hppr HRA HG01) as [HS SHOK].
pose proof HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _ & _).
pose proof Hstk as (Hal & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (app_addr_below_ceil p (Happ p ltac:(lia))) as Hp0.
assert (Rv0 : 0 <= v0 < 256) by exact (proj2 (HG01 0%nat ltac:(cbn; lia))).
assert (Rv1 : 0 <= v1 < 256) by exact (proj2 (HG01 1%nat ltac:(cbn; lia))).
remember (EA regs v0 v1) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold EA; apply Eimg_env).
assert (EL : forall n, (n < A_TEXT)%nat -> ew E n = ew (Ereg regs (alloc_extra v0 v1)) n)
by (intros n Hn; subst E; unfold EA; apply Eimg_low; exact Hn).
assert (E1 : ew E 1 = getr regs 1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 1 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 p) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 base) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E12 : ew E 12 = Z_to_bv 64 in_ch) by (rewrite EL by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 12 12%bv eq_refl); exact H12).
assert (E33 : ew E 33 = Z_to_bv 64 v0) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 v1) by (rewrite EL by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (HAE : env_agree 32 (Ereg regs (alloc_extra v0 v1)) E)
by (split; [intros n Hn; apply EL; unfold A_TEXT; lia | subst E; unfold EA; reflexivity]).
clear HE EL.
unfold cfg_at. change (w64 (BASE + AF_reac_grant_allocate)) with (Z_to_bv 64 (BASE + AF_reac_grant_allocate)).
let rec go := idtac;
lazymatch goal with HSx : st_ok_pi _ _ _ _ _, HJx : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
paj_run_tok RUN HSx HJx SHOK alloc_span; [awr_alloc sp0 (spZ regs) p Usp E10 HpW |];
lazymatch goal with
| HSy : st_ok_pi _ _ _ ?ss _ |- _ =>
let K := eval vm_compute in (run_K A_LIM Bxa alloc_SH ss) in
let why := lazymatch paj_tables RUN with (?tpi, ?tw) => psym_why_tok tpi tw K Bxa alloc_span alloc_SH (start K Bxa alloc_span alloc_SH ss) end in
let pc := eval vm_compute in (ss_pc ss) in
lazymatch why with
| SR_jalr _ =>
repeat match goal with
| H : branch_taken BC_LTU (sv_denot ?Ez (SAluw ALU_ADD (SOff 12 0) (SLit (-41)))) (sv_denot ?Ez (SLit 18446744073709551576)) = _ |- _ =>
let Q := fresh "Q" in assert (Q : ew Ez 12 = Z_to_bv 64 in_ch)
by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E12);
rewrite (cond_bw Ez in_ch Q Hc32) in H; clear Q
| H : branch_taken BC_LT (sv_denot ?Ez (SOff 11 0)) (sv_denot ?Ez (SLit 0)) = _ |- _ =>
let Q := fresh "Q" in assert (Q : ew Ez 11 = Z_to_bv 64 base)
by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E11);
rewrite (cond_bb Ez base Q Hb32) in H; clear Q
end;
zbool_a;
try (match goal with H : branch_taken BC_LT (sv_denot ?Ez (SLit 48)) (sv_denot ?Ez (SAluw ALU_ADD (SOff 12 0) (SOff 11 0))) = _ |- _ =>
let Q1 := fresh "Q" in let Q2 := fresh "Q" in
assert (Q1 : ew Ez 11 = Z_to_bv 64 base)
by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E11);
assert (Q2 : ew Ez 12 = Z_to_bv 64 in_ch)
by (cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; exact E12);
rewrite (cond_bs Ez base in_ch Q1 Q2 ltac:(unfold int32 in Hb32; lia) ltac:(lia)
ltac:(pose proof (Hovf ltac:(lia) ltac:(lia)); lia)) in H; clear Q1 Q2 end);
zbool_a;
let HFI := fresh "HFI" in
destruct (fits base in_ch) eqn:HFI;
[ try (exfalso; unfold fits in HFI; zbool_a; zbool_a; zbool_a; zbool_a; lia)
| try (exfalso; unfold fits in HFI; zbool_a; zbool_a; zbool_a; zbool_a; lia) ];
lazymatch goal with HSz : st_ok_pi _ _ _ _ (restrict _ ?msc), HJz : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
prreg HSz (10%bv : bv 5) R10; prreg HSz (1%bv : bv 5) R1;
eapply (RET W _ _ _ _ _ HSz eq_refl ltac:(vm_compute; reflexivity));
let mq := fresh "mat" in intros mq;
split; [reflexivity|];
exists (ms_regs msc), (ms_mem msc); eexists;
split; [cbn [ms_regs]; rewrite R1; cbn [ew ewset Nat.eqb]; rewrite ?ew_ewset_other by lia; rewrite E1, Hra; reflexivity|];
split; [unfold EV_ALLOC; rewrite Z.add_0_r; cbn [ms_mem];
apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJz|];
split; [eapply (aregs_preserved_of_st_ok SEGS _ _ _ _ regs (alloc_extra v0 v1) HSz);
[ split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; apply (proj1 HAE); lia
| cbn [ed ewset]; apply (proj2 HAE)]
| vm_compute; reflexivity ]|];
split; [cbn [ms_regs]; rewrite R10, HFI; apply bv_eq; vm_compute; reflexivity|];
rewrite HFI;
lazymatch type of HSz with
| st_ok_pi ?sg ?vl ?Ez ?ssx (restrict ?Hh ?msy) =>
let HMO := fresh "HMO" in
pose proof (st_ok_mem_ok sg Ez (abs_ss vl ssx) (restrict Hh msy) HSz) as HMO;
cbn [abs_ss setpc ss_mem restrict ms_mem] in HMO;
destruct HMO as (_ & HMO & _);
let l := eval vm_compute in (ss_mem ssx) in change (ss_mem ssx) with l in HMO;
apply Forall_inv_tail in HMO; apply Forall_inv_tail in HMO; apply Forall_inv_tail in HMO;
apply Forall_inv in HMO;
destruct HMO as (_ & _ & _ & HMO);
let Hc1 := fresh "Hch" in let Hc2 := fresh "Hch" in
pose proof (Forall_inv HMO) as Hc1; pose proof (Forall_inv (Forall_inv_tail HMO)) as Hc2;
let Hb10 := fresh "Hb10" in
assert (Hb10 : base_val Ez (Some 10%nat) = p)
by (cbn [base_val]; rewrite ?ew_ewset_other by lia; rewrite E10; apply unsigned_lit_small; lia);
cbn [YP09.r_base YP09.c_off YP09.c_val] in Hc1, Hc2; rewrite Hb10 in Hc1, Hc2;
let D33 := fresh "D" in let D34 := fresh "D" in let D11 := fresh "D" in let D12 := fresh "D" in
assert (D33 : sv_denot Ez (SOff 33 0) = Z_to_bv 64 v0)
by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
assert (D34 : sv_denot Ez (SOff 34 0) = Z_to_bv 64 v1)
by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
assert (D11 : sv_denot Ez (SOff 11 0) = Z_to_bv 64 base)
by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E11, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
assert (D12 : sv_denot Ez (SOff 12 0) = Z_to_bv 64 in_ch)
by (cbn [sv_denot]; rewrite ?ew_ewset_other by lia; rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity);
split;
[ first [ exact (garr8_two Ez _ p base in_ch _ _ Hc1 Hc2 D11 D12)
| exact (garr8_two Ez _ p base in_ch _ _ Hc2 Hc1 D11 D12)
| (replace [v0; v1] with [v0 mod 256; v1 mod 256] by (rewrite (Z.mod_small v0 256), (Z.mod_small v1 256) by lia; reflexivity);
first [ exact (garr8_two Ez _ p v0 v1 _ _ Hc1 Hc2 D33 D34)
| exact (garr8_two Ez _ p v0 v1 _ _ Hc2 Hc1 D33 D34) ]) ]
| ];
let HM := fresh "HM" in
assert (HM : forall xx : word, ~ (spZ regs - TALLOC_STK <= bv_unsigned xx < spZ regs) ->
~ (p <= bv_unsigned xx < p + 2) -> mrestrict Hh (ms_mem msy) xx = mrestrict Hh memc xx);
[ intros xx HA HB; rewrite WS in HA;
repeat match goal with
| Hf : frame_of ?Ew ?rsw (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mB) |- mrestrict ?Hq ?mB xx = _ =>
rewrite (Hf xx ltac:(let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr); vm_compute in Hin;
repeat (destruct Hin as [Hin | Hin];
[ subst r; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
rewrite ?ew_ewset_other in Hr by lia; rewrite ?Usp, ?E10 in Hr;
rewrite ?unsigned_lit_small in Hr by lia; lia |]);
destruct Hin)); clear Hf
end; reflexivity
| ];
let HGr := fresh "HGr" in
assert (HGr : mem_grows (mrestrict Hh memc) (mrestrict Hh (ms_mem msy)));
[ repeat match goal with
| Hg : mem_grows (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mB) |- mem_grows (mrestrict ?Hq ?mA) (mrestrict ?Hq ?mC) =>
first [ exact Hg | eapply mem_grows_trans; [exact Hg |] ]
end; apply mem_grows_refl
| ];
unfold tcj_kept;
split;
[ intros aa Haa Hww Hee; apply aview_of_eq; apply HM;
rewrite unsigned_lit_small by lia; lia |];
split;
[ intros bb mm ii Hin Hii Hee;
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb mm HAR Hin) as (_ & Hb4096 & Hbceil & _);
apply aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; lia |];
split;
[ intros aa Hin _ _; pose proof (pa_img_range aa Hin) as Hir;
apply aview_of_eq; apply HM; rewrite unsigned_lit_small by lia;
unfold off_img in Hoff; lia |];
split;
[ intros cid pos aa Hin Hrr Hee;
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (Hf0 & Hfc & _);
pose proof (fs_frame_bytes_nonneg cid) as Hfb;
pose proof (shadow_addr_bounds (frame_addr lyc cid pos) ltac:(lia)) as Hs1;
pose proof (shadow_addr_bounds (frame_addr lyc cid pos + fs_frame_bytes cid) ltac:(lia)) as Hs2;
pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfb) as Hs3;
unfold in_zr, frame_rng in Hrr; cbn [fst snd] in Hrr;
apply aview_of_eq; apply HM; rewrite unsigned_lit_small by lia; destruct Hrr as [Hrr|Hrr]; lia |];
split;
[ intros aa _ _ Hpr; exact (apresent_grows Hh memc (ms_mem msy) aa HGr Hpr) |];
intros aa Haa;
pose proof HJz as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _);
apply Hpres2; lia
end
end
| SR_branch _ _ _ => psrr_branch_tok RUN BR HSy SHOK alloc_span; [go | go]
| _ => idtac "STUCK" pc why; fail
end
end end in go.
Qed.
End e.
End d.
End b.
