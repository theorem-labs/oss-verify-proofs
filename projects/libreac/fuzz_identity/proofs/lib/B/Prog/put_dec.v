(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8c.v:168-170
   [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC95.v:145-147 [Apache-2.0];
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC9z.v:176-178 [Apache-2.0]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC1f.v:361-366
   [Apache-2.0 OR MIT]; projects/cgif/cgif_file_fuzzer/proofs/lib/YC85.v:371-373 [Apache-2.0 OR MIT];
   projects/cgif/cgif_file_fuzzer/proofs/lib/YC8a.v:360-365 [Apache-2.0 OR MIT], for libreac/fuzz_identity's asan-ubsan
   build (lib/B). The [Apache-2.0 OR MIT] text is used under Apache-2.0. The same text also appears in
   projects/cgif/cgif_file_fuzzer/proofs/lib/A/AC8b.v:341-344; projects/cgif/cgif_file_fuzzer/proofs/lib/A/ACa2.v:176-177. *)
(* put_dec of fuzz_identity.asan-ubsan (build B), at BASE + AF_put_dec = 0x828ac: the contract AND its walk.
   put_dec writes bytes of its caller's frames (b + n .. b + n + dec_len v mn) and of the caller's machine
   stack (the 8 bytes at p), so it is stated in cgif's caller-journal form (IdentBCJ.v: twr_ok, tsrc_ok,
   tcj_kept), not in the afn_pre / apost_base form.
   The walk is five segments of the listing, one lemma each, chained by SRr_bind in pb_put_dec:
   pd_entry (0x2138..0x2254, the prologue and the class-0 side-stack frame), pd_dloop (0x2254..0x22b0, the
   digit loop), pb_pd_pad (0x22b0..0x2304, the zero padding), pd_copy_seg (0x2304..0x2398, the copy-out)
   and pd_tail (0x2398..0x242c, the frame release and the epilogue). *)

From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI16.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YI00 YI08 YI09 YI0s YI0t YI0m YI0n YP0g YImgTop.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBCJ IdentBFrame YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YO0a YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
Ltac pd_slot HS od rr Hu :=
lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ssx (restrict ?Hh ?msx) =>
let V := fresh "V" in
pose proof (@field_of_region_any sg Ex (ms_mem (restrict Hh msx)) 2%nat _ _ (-96) 0 (-96) 0 od 8%N (SOff rr 0)
(st_ok_pi_region_nth Ex ssx _ 2%nat _ HS eq_refl) Hu
ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as V;
cbn [ms_mem restrict] in V; cbn [sv_denot] in V;
rewrite ?Z.add_0_r in V;
repeat match goal with H : ew _ rr = _ |- _ => rewrite H in V end;
rewrite ?Z_to_bv_bv_unsigned, ?Z_to_bv64_canon, ?Z_to_bv_bv_unsigned in V;
replace (8 * Z.of_N 8) with 64 in V by reflexivity;
rewrite Z.mod_small in V by (apply bv_unsigned_in_range);
first [ exact V
| lazymatch type of V with val_mem _ _ (?sp + _) _ _ => replace (sp + od) with (sp - (- od)) in V by lia; exact V end
| fail 1 "pd_slot: the saved word does not match" ]
end.
Ltac pd_reg HS :=
lazymatch goal with
| |- getr (ms_regs ?m) ?r = _ =>
let T := fresh "TT" in
prreg HS r T; cbn [ms_regs] in T; rewrite T; clear T;
rewrite ?Z.add_0_r;
repeat match goal with H : ew _ _ = _ |- _ => rewrite H end;
repeat match goal with H : bv_unsigned (ew _ _) = _ |- _ => rewrite H end;
rewrite ?unsigned_lit_small by (unfold SB; lia);
first [ reflexivity
| unfold w64; f_equal; first [ reflexivity | apply zcanon_id; unfold M64; lia | lia ] ]
end.
(* The digit loop of put_dec in fuzz_identity.asan-ubsan (build B): listing offsets 0x2254 .. 0x22b0,
   i.e. addresses 0x829c8 (the loop head) .. 0x82a24 (where the code leaves the loop).  Scratch file
   of a Theorem Labs lane; the statement is glued into lib/B/Prog/put_dec.v. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YM05 YI00 YI08 YI09 YI0s YI0t YI0m YI0n YP0g.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require Import IdentSpec.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require put_dec_c put_dec.
Import OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog.put_dec_c(dec_len).
(* --- the loop's symbolic state, its shadow entry, and the registers it leaves alone ------------- *)
(* t1 = 10, t2 = 0xcccccccd << 32 and t3 = 9 are pinned as literals: the engine folds the
   multiply-high-by-magic sequence and the loop test only with the concrete constants. *)
Definition dl_sr : list sv :=
  sr_set (sr_set (sr_set sr_atoms 6%bv (SLit 10)) 7%bv (SLit 14757395259826634752)) 28%bv (SLit 9).
(* one region: the single digit byte the iteration stores, based on atom 5 (t0 = D + i) *)
Definition dl_regions : smem := [YP09.mkRegion (Some 5%nat) 0 1 0 1 []].
Definition dl_facts : facts :=
  mkFacts [(5%nat, mkAF 4096 (2 ^ 47 - 1) 0); (11%nat, mkAF 4096 (2 ^ 47 - 1) 0); (16%nat, mkAF 0 9 0);
           (22%nat, mkAF SB SB 0)] [] [].
Definition ss_dl : sstate := mkSS 0x2254 dl_sr dl_regions None dl_facts.
(* reversed entry: its range_addressable half is vacuous, its app_apart half carries the frame *)
Definition dl_SH : list shent := [mkSHE 5 1 0].
Definition dl_Bx : sv := SOff 22 0.
Definition DL_KEPT : list (bv 5) := [1; 2; 3; 4; 8; 9; 10; 12; 13; 14; 15; 18; 19; 20; 22; 23; 24; 25; 26; 27]%bv.
(* --- the arithmetic of one iteration, at the level of the symbolic valuation -------------------- *)
Lemma dl_u21 : forall (E : env) (xw : word), ew E 21 = xw -> U E (SOff 21 0) = bv_unsigned xw.
Proof.
intros E xw H. pose proof (u64_range xw). rewrite U_SOff, H, Z.add_0_r. apply zcanon_id. unfold M64. lia.
Qed.
Lemma dl_U_q : forall (E : env) (xw : word) (x : Z),
  ew E 21 = xw -> bv_unsigned xw mod 2 ^ 32 = x ->
  U E (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 14757395259826634752)) (SLit 35))
  = x / 10.
Proof.
intros E xw x H21 EX. pose proof (u64_range xw) as Hu.
pose proof (dl_u21 E xw H21) as U21.
assert (Hx : 0 <= x < 2 ^ 32) by (rewrite <- EX; apply Z.mod_pos_bound; lia).
assert (Hq : 0 <= x / 10 < 429496730) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SMd. cbn [zmd_raw Z.of_N]. rewrite U_SAlu. cbn [zalu_raw].
rewrite U21, !U_SLit.
rewrite (zcanon_id 32), (zcanon_id 35), (zcanon_id 14757395259826634752) by (unfold M64; lia).
change (Z.land 32 63) with 32. change (Z.land 35 63) with 35.
rewrite Z.shiftl_mul_pow2 by lia.
assert (S1 : zcanon (bv_unsigned xw * 2 ^ 32) = x * 2 ^ 32).
{ unfold zcanon, M64. change (2 ^ 64) with (2 ^ 32 * 2 ^ 32).
  rewrite Z.mul_mod_distr_r by lia. rewrite EX. reflexivity. }
rewrite S1.
assert (S2 : zcanon (Z.shiftr (x * 2 ^ 32 * 14757395259826634752) 64) = x * 3435973837).
{ rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2 ^ 32 * 14757395259826634752) with (x * 3435973837 * 2 ^ 64) by lia.
  rewrite Z.div_mul by lia. apply zcanon_id. unfold M64.
  change (2 ^ 32) with 4294967296 in Hx. change (2 ^ 64) with 18446744073709551616. nia. }
rewrite S2. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 35) with 34359738368.
rewrite (put_dec.div10_magic x ltac:(change (2 ^ 32) with 4294967296 in Hx; lia)).
apply zcanon_id. unfold M64. lia.
Qed.
Lemma dl_U_dig : forall (E : env) (xw : word) (x : Z),
  ew E 21 = xw -> bv_unsigned xw mod 2 ^ 32 = x ->
  U E (SAlu ALU_OR
        (SAluw ALU_SUB (SOff 21 0)
          (SMd M_MUL
            (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 14757395259826634752))
              (SLit 35))
            (SLit 10)))
        (SLit 48))
  = 48 + x mod 10.
Proof.
intros E xw x H21 EX. pose proof (u64_range xw) as Hu.
pose proof (dl_u21 E xw H21) as U21. pose proof (dl_U_q E xw x H21 EX) as UQ.
assert (Hx : 0 <= x < 2 ^ 32) by (rewrite <- EX; apply Z.mod_pos_bound; lia).
assert (Hq : 0 <= x / 10 < 429496730) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hr.
assert (Hdm : 10 * (x / 10) + x mod 10 = x) by (symmetry; apply Z.div_mod; lia).
assert (UM : U E (SMd M_MUL
  (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 14757395259826634752)) (SLit 35))
  (SLit 10)) = 10 * (x / 10)).
{ rewrite U_SMd. cbn [zmd_raw]. rewrite UQ, U_SLit, (zcanon_id 10) by (unfold M64; lia).
  rewrite (Z.mul_comm (x / 10) 10). apply zcanon_id. unfold M64. lia. }
assert (US : U E (SAluw ALU_SUB (SOff 21 0)
  (SMd M_MUL
    (SAlu ALU_SRL (SMd M_MULHU (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 14757395259826634752)) (SLit 35))
    (SLit 10))) = x mod 10).
{ rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite UM, U21, EX.
  rewrite (Z.mod_small (10 * (x / 10)) (2 ^ 32)) by lia.
  replace (x - 10 * (x / 10)) with (x mod 10) by lia.
  rewrite swrap32_id by lia. apply wrap64_id. unfold M64. lia. }
rewrite U_SAlu. cbn [zalu_raw]. rewrite US, U_SLit, (zcanon_id 48) by (unfold M64; lia).
assert (C : x mod 10 = 0 \/ x mod 10 = 1 \/ x mod 10 = 2 \/ x mod 10 = 3 \/ x mod 10 = 4 \/
            x mod 10 = 5 \/ x mod 10 = 6 \/ x mod 10 = 7 \/ x mod 10 = 8 \/ x mod 10 = 9) by lia.
repeat destruct C as [C|C]; rewrite C; reflexivity.
Qed.
Lemma dl_U_inc : forall (E : env) (i : Z), ew E 17 = Z_to_bv 64 i -> 0 <= i < 10 ->
  U E (SAluw ALU_ADD (SOff 17 0) (SLit 1)) = i + 1.
Proof.
intros E i H17 Hi.
assert (U17 : U E (SOff 17 0) = i)
  by (rewrite U_SOff, H17, Z.add_0_r, unsigned_lit_small by lia; apply zcanon_id; unfold M64; lia).
rewrite U_of_S, S_SAluw. cbn [zalu_raw]. rewrite U17, U_SLit, (zcanon_id 1) by (unfold M64; lia).
rewrite !(Z.mod_small _ (2 ^ 32)) by lia. rewrite swrap32_id by lia. apply wrap64_id. unfold M64. lia.
Qed.
Lemma dl_ltu9 : forall (E : env) (xw : word) (x : Z),
  ew E 21 = xw -> bv_unsigned xw mod 2 ^ 32 = x -> (bv_unsigned xw < 2 ^ 32 \/ 10 <= x) ->
  (U E (SLit 9) <? U E (SOff 21 0)) = (10 <=? x).
Proof.
intros E xw x H21 EX HX. pose proof (u64_range xw) as Hu.
rewrite (dl_u21 E xw H21), U_SLit, (zcanon_id 9) by (unfold M64; lia).
assert (Hx : 0 <= x < 2 ^ 32) by (rewrite <- EX; apply Z.mod_pos_bound; lia).
destruct (Z.leb_spec 10 x) as [H|H].
- apply Z.ltb_lt. pose proof (Z.mod_le (bv_unsigned xw) (2 ^ 32) ltac:(lia) ltac:(lia)). lia.
- apply Z.ltb_ge. destruct HX as [HX|HX]; [|lia]. rewrite Z.mod_small in EX by lia. lia.
Qed.
Lemma dl_dg : forall r, 0 <= r < 10 -> bv_unsigned (dg r) = 48 + r.
Proof.
intros r Hr. unfold dg. rewrite Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 8) with 256. apply Z.mod_small. lia.
Qed.
Lemma dl_garr8_one : forall segs (m : word -> option byte) a v,
  val_mem segs m a 1 v -> 0 <= v < 256 -> garr8 segs m a [v].
Proof.
intros segs m a v Hv Hr j Hj. cbn [length] in Hj. assert (Hj0 : j = 0%nat) by lia. subst j.
cbn [nth]. rewrite Z.add_0_r. split; [exact Hv | exact Hr].
Qed.
Lemma dl_unsig_U : forall (E : env) (v : sv), bv_unsigned (sv_denot E v) = U E v.
Proof. reflexivity. Qed.
(* prreg, but without prreg_norm: it keeps the register's value as  sv_denot E <sv>, which the
   U-level lemmas above rewrite. *)
Ltac dl_reg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in
  change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.
(* put_dec of fuzz_identity.asan-ubsan (build B): the zero-padding segment, listing offsets 0x22b0 .. 0x2304
   (addresses 0x82a24 .. 0x82a78).  0x82a24 compares the digit count a7 with the minimum width s4 and skips
   the pad loop when the count is already big enough; otherwise a7 := mn - k and the loop at 0x82a38 checks
   the shadow byte of a1, stores '0' at t0, steps a1/t0 and counts a7 down.  0x82a70 sets a6 to the larger of
   s4 and a6.  The released UBSan walk's plU (lib/U/Prog/put_dec.v) is the functional reference for the loop
   invariant; this is the ASan+UBSan machine-code walk in the caller-journal form. *)
(* The copy-out segment of put_dec in fuzz_identity.asan-ubsan (build B): listing offsets 0x2304 .. 0x2398
   (addresses 0x82a78 .. 0x82b0c).  The segment complements b, sets a6 = K - 1, t0 = 10, t1 = the shadow
   address of p and t2 = -1, then runs the byte loop at 0x82a90: it reads d[a6], bumps the 8-byte counter at
   p and stores the byte at b + N + j, until a6 wraps to -1.  Three UBSan traps (0x82a94, 0x82a98, 0x82ac8)
   and three ASan shadow checks are on the path; the traps are shown not taken and the shadow checks are
   discharged by the token engine.  The released UBSan-build walk lib/U/Prog/put_dec.v (clU, bne_m1) is the
   functional reference for the invariant. *)
(* The registers the segment leaves alone: it writes t0, t1, t2, a1, a6, a7, t3, t4, t5. *)
Definition PD_CL_KEPT : list (bv 5) :=
  [1; 2; 3; 4; 8; 9; 10; 12; 13; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%bv.
(* The loop body alone keeps a7 (= the complement of b) too. *)
Definition PD_CLB_KEPT : list (bv 5) :=
  [1; 2; 3; 4; 8; 9; 10; 12; 13; 14; 15; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 31]%bv.
(* Atom 22 is s6 = SHADOW_OFF, the shadow base the ASan checks of this segment use. *)
Definition cl_Bx : sv := SOff 22 0.
(* The symbolic state at the loop head 0x231c (address 0x82a90).  Atoms 32 .. 35 are the four extra values:
   the counter at p, the destination byte's address, the digit's address and the digit. *)
Definition cl_regs : list sv :=
  sr_set (sr_set (sr_set sr_atoms (5%bv : bv 5) (SLit 10))
    (6%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SOff 18 0) (SLit 3)) (SOff 22 0)))
    (7%bv : bv 5) (SLit 18446744073709551615).
Definition cl_mem : smem :=
  [ YP09.mkRegion (Some 18%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 34%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 35 0))];
    YP09.mkRegion (Some 33%nat) 0 1 0 1 [] ].
Definition cl_facts : facts :=
  mkFacts [ (14%nat, mkAF 0 (2 ^ 47) 0); (15%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0); (16%nat, mkAF 0 9 0);
            (17%nat, mkAF (2 ^ 63) (2 ^ 64 - 1) 0); (18%nat, mkAF 0 (2 ^ 47 - 16) 3);
            (19%nat, mkAF 0 (2 ^ 63 - 1) 0); (22%nat, mkAF SB SB 0); (32%nat, mkAF 0 (2 ^ 63 - 2) 0);
            (33%nat, mkAF 0 (2 ^ 47 - 2) 0); (34%nat, mkAF 0 (2 ^ 47 - 2) 0); (35%nat, mkAF 0 255 0) ]
    []
    [ (SAlu ALU_ADD (SOff 14 0) (SOff 16 0), SOff 34 0); (SAlu ALU_ADD (SOff 19 0) (SOff 32 0), SOff 33 0) ].
Definition cl_ss : sstate := mkSS 0x231c cl_regs cl_mem None cl_facts.
Definition cl_SH : list shent := [mkSHE 18 0 8; mkSHE 33 0 1].
(* The symbolic state at the segment's entry 0x2304 (address 0x82a78): registers only. *)
Definition cl_ssu : sstate := mkSS 0x2304 sr_atoms [] None (mkFacts [(22%nat, mkAF SB SB 0)] [] []).
Lemma cl_denot_of_U : forall (E : env) (v : sv) (z : Z), U E v = z -> sv_denot E v = Z_to_bv 64 z.
Proof. intros E v z Hz. rewrite <- Hz. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.
(* prreg, but without prreg_norm's  cbn [sv_denot], which would destroy an SAlu tree. *)
Ltac prregR HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in
change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr
end.
(* The write rights of this segment's two writable regions: the counter at p and the byte at b + N + j. *)
Ltac cl_awr HWPh HWBh U18h U33h :=
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 18%nat _);
[ reflexivity
| rewrite ?ew_ewset_other by lia; exact U18h
| cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; exact (proj1 (HWPh aa ltac:(lia)))
| apply awr_ok_cons_ro; [cbn; lia|];
eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 33%nat _);
[ reflexivity
| rewrite ?ew_ewset_other by lia; exact U33h
| cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; exact (proj1 (HWBh aa ltac:(lia)))
| apply awr_ok_nil ] ].
(* The shadow bytes this segment's checks read all lie in the shadow band [SHADOW_OFF, kHighShadowEnd). *)
Lemma cl_ra_band : forall (rd rd' : Z -> option Z) a n,
(forall s, SHADOW_OFF <= s < kHighShadowEnd -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 ->
range_addressable rd SHADOW_OFF a n -> range_addressable rd' SHADOW_OFF a n.
Proof.
intros rd rd' a n HK Ha Han HR x Hx. destruct (HR x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
rewrite <- Hs. apply HK. unfold shadow_of_addr, SHADOW_OFF, kHighShadowEnd in *.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)).
assert (x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.
Lemma cl_hull_band : forall (rd rd' : Z -> option Z) a n,
(forall s, SHADOW_OFF <= s < kHighShadowEnd -> rd' s = rd s) -> 0 <= a -> a + n <= 2 ^ 47 -> 0 < n ->
shadow_hull_vis rd a n -> shadow_hull_vis rd' a n.
Proof.
intros rd rd' a n HK Ha Han Hn HV s Hs. rewrite HK; [exact (HV s Hs)|].
unfold shadow_addr, SHADOW_OFF, kHighShadowEnd in *.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)).
pose proof (Z.div_lt_upper_bound (a + n - 1) 8 (2 ^ 44) ltac:(lia) ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + a / 8) 8 ltac:(lia)).
pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + a / 8) 8).
pose proof (Z.mod_pos_bound (2147450880 + a / 8) 8 ltac:(lia)).
pose proof (Z_div_mod_eq_full (2147450880 + (a + n - 1) / 8) 8).
pose proof (Z.mod_pos_bound (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)). lia.
Qed.
(* An app-memory range never meets the shadow band. *)
Lemma cl_amem_out_band : forall q n a, amem_range q n -> q <= a < q + n -> ~ (SHADOW_OFF <= a < kHighShadowEnd).
Proof.
intros q n a Hr Ha. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Hr.
unfold SHADOW_OFF, kHighShadowEnd. lia.
Qed.
(* The symbolic state at 0x2398.  Registers keep their atoms, except a0, which the state names by a2's atom 12
   (both hold F).  Atom 32 is the flag address FL; atoms 33 .. 40 are the saved ra, s0, s1, s2, s3, s4, s5, s6.
   Regions: the frame F (writes [F, F + 8), the flag pointer at F + 56), the frame's shadow (8 bytes, all
   written), the flag byte (written), and the read-only save area [s0 - 64, s0) of the machine frame. *)
Definition pt_regs : list sv := sr_set sr_atoms (10%bv : bv 5) (SOff 12 0).
Definition pt_mem : smem :=
  [ YP09.mkRegion (Some 12%nat) 0 64 0 8 [YP09.mkChunk 56 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 13%nat) 0 8 0 8 [];
    YP09.mkRegion (Some 32%nat) 0 1 0 1 [];
    YP09.mkRegion (Some 8%nat) (-64) 0 0 0
      [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
       YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
       YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
       YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0))] ].
Definition pt_facts : facts := mkFacts [ (12%nat, HPTR 0) ] [] [].
Definition pt_ss : sstate := mkSS 0x2398 pt_regs pt_mem None pt_facts.
Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section d.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Lemma cl_val_mem_kept : forall (H : word -> bool) (m m' : word -> option byte) a n v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS H m' x = aview SEGS H m x) ->
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H m') a n v.
Proof.
intros H m m' a n v HK HV k Hk.
rewrite (mbyte_of_aview SEGS H H m m' (a + Z.of_nat k) (HK (a + Z.of_nat k) ltac:(lia))).
exact (HV k Hk).
Qed.
Lemma cl_garr8_kept : forall (H : word -> bool) (m m' : word -> option byte) a l,
(forall x, a <= x < a + Z.of_nat (length l) -> aview SEGS H m' x = aview SEGS H m x) ->
garr8 SEGS (mrestrict H m) a l -> garr8 SEGS (mrestrict H m') a l.
Proof.
intros H m m' a l HK HG. apply (garr8_frame SEGS (mrestrict H m)); [exact HG|].
intros x Hx. exact (mbyte_of_aview SEGS H H m m' x (HK x Hx)).
Qed.
Section e.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes SEGS B 0.
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let errno_low := pal_env B TL.
Let RUN := paj_run B LAWS. Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).
Let RUNP := SRr_run_pi_AJ B LAWS. Let RUNTOP := SRr_run_to_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.

Definition PUT_DEC_STK : Z := 112 + ESTACK.
(* Events: stack_malloc_0 keeps st_nev, the frame release keeps it; B pads with an inline loop, so
   there is no __asan_memset call to charge either. *)
Definition EV_PUT_DEC : Z := 0.

Definition tput_dec_post (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (k : Z)
  (regs : bvmap 5 word) (b p n v mn : Z) : world SEGS -> config -> Prop :=
  fun W2 c2 => exists ly2 S2 regs2 mem2 md2,
    c2 = mkCfg (mkst regs2 (getr regs 1) mem2 (seg_rom SEGS)) md2 /\
    ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own ly2 S2 W2 mem2 md2 (k + EV_PUT_DEC) /\
    aregs_preserved regs regs2 /\ frames S2 = frames Sc /\ ablocks B ly2 S2 = ablocks B lyc Sc /\
    tcj_kept B PUT_DEC_STK lyc Sc W memc W2 mem2 (spZ regs)
      (fun a => p <= a < p + 8 \/ b + n <= a < b + n + dec_len v mn) /\
    garr8 SEGS (mrestrict (w_H W2) mem2) (b + n) (map bv_unsigned (DEC v mn)) /\
    val_mem SEGS (mrestrict (w_H W2) mem2) p 8 (n + dec_len v mn).

Definition tput_dec_spec : Prop :=
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (b p n v mn : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 b -> getr regs 11 = w64 p ->
  bv_unsigned (getr regs 12) mod 2 ^ 32 = v -> (bv_unsigned (getr regs 12) < 2 ^ 32 \/ 10 <= v) ->
  getr regs 13 = w64 mn -> 0 <= mn <= 10 ->
  spZ regs mod 32 = 0 -> sp0 - STK <= spZ regs - PUT_DEC_STK -> spZ regs <= sp0 ->
  Z.of_nat (length (frames Sc)) <= 8 ->
  p mod 8 = 0 -> 0 <= b -> 0 <= n ->
  val_mem SEGS (mrestrict (w_H W) memc) p 8 n ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) p 8 ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc (spZ regs) (b + n) (dec_len v mn) ->
  tsrc_ok W memc (spZ regs) p 8 ->
  tsrc_ok W memc (spZ regs) (b + n) (dec_len v mn) ->
  (p + 8 <= b + n \/ b + n + dec_len v mn <= p) ->
  (spZ regs <= p \/ p + 8 <= spZ regs - PUT_DEC_STK) ->
  (spZ regs <= b + n \/ b + n + dec_len v mn <= spZ regs - PUT_DEC_STK) ->
  st_nev Sc + EV_PUT_DEC <= EV_MAX ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_put_dec) regs memc mdc)
    (tput_dec_post STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs b p n v mn).

(* ---- Entry ---- *)
Definition pd_ss : sstate :=
  mkSS AF_put_dec sr_atoms
    [ stack_region 96; got_regionP; bcell_regionP 32; uar_got_regionP 33; uar_cell_regionP 33 ] None
    (mkFacts [ (2%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (13%nat, mkAF 0 10 0);
               (32%nat, mkAF SB SB 0); (33%nat, mkAF 4096 140737479966720 2) ] [] []).

Lemma pd_entry :
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs : bvmap 5 word) (p b mn : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  getr regs 10 = w64 b -> getr regs 11 = w64 p -> getr regs 13 = w64 mn ->
  0 <= mn <= 10 ->
  spZ regs mod 32 = 0 -> sp0 - STK <= spZ regs - PUT_DEC_STK -> spZ regs <= sp0 ->
  Z.of_nat (length (frames Sc)) <= 8 ->
  SRr SEGS W (cfg_at SEGS (BASE + AF_put_dec) regs memc mdc)
  (fun W' c' => W' = W /\ exists S2 pos regs' mem' md',
     c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x2254)) mem' (seg_rom SEGS)) md' /\
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem' md' k /\
     frames S2 = (0, pos) :: frames Sc /\ ablocks B lyc S2 = ablocks B lyc Sc /\
     st_nev S2 = st_nev Sc /\ blocks_bytes S2 = blocks_bytes Sc /\
     getr regs' 2 = Z_to_bv 64 (spZ regs - 96) /\
     getr regs' 3 = w64 (as_gp B) /\ getr regs' 4 = w64 (as_tp B) /\
     getr regs' 5 = w64 (frame_addr lyc 0 pos + 32) /\ getr regs' 6 = w64 10 /\
     getr regs' 7 = w64 14757395259826634752 /\
     getr regs' 8 = Z_to_bv 64 (spZ regs) /\ getr regs' 9 = Z_to_bv 64 (spZ regs - 96) /\
     getr regs' 10 = w64 (frame_addr lyc 0 pos) /\ getr regs' 11 = w64 (frame_addr lyc 0 pos + 32) /\
     getr regs' 12 = w64 (frame_addr lyc 0 pos) /\
     getr regs' 13 = w64 (SB + frame_addr lyc 0 pos / 8) /\
     getr regs' 14 = w64 (frame_addr lyc 0 pos + 32) /\
     getr regs' 15 = Z_to_bv 64 (- (frame_addr lyc 0 pos + 32) - 1) /\
     getr regs' 16 = w64 0 /\ getr regs' 17 = w64 0 /\
     getr regs' 18 = w64 p /\ getr regs' 19 = w64 b /\ getr regs' 20 = w64 mn /\
     getr regs' 21 = getr regs 12 /\ getr regs' 22 = w64 SB /\
     getr regs' 23 = getr regs 23 /\ getr regs' 24 = getr regs 24 /\
     getr regs' 25 = getr regs 25 /\ getr regs' 26 = getr regs 26 /\
     getr regs' 27 = getr regs 27 /\
     getr regs' 28 = w64 9 /\ getr regs' 29 = w64 2 /\
     val_mem SEGS (mrestrict (w_H W) mem') (spZ regs - 8) 8 (bv_unsigned (getr regs 1)) /\
     val_mem SEGS (mrestrict (w_H W) mem') (spZ regs - 16) 8 (bv_unsigned (getr regs 8)) /\
     val_mem SEGS (mrestrict (w_H W) mem') (spZ regs - 24) 8 (bv_unsigned (getr regs 9)) /\
     val_mem SEGS (mrestrict (w_H W) mem') (spZ regs - 32) 8 (bv_unsigned (getr regs 18)) /\
     val_mem SEGS (mrestrict (w_H W) mem') (spZ regs - 40) 8 (bv_unsigned (getr regs 19)) /\
     val_mem SEGS (mrestrict (w_H W) mem') (spZ regs - 48) 8 (bv_unsigned (getr regs 20)) /\
     val_mem SEGS (mrestrict (w_H W) mem') (spZ regs - 56) 8 (bv_unsigned (getr regs 21)) /\
     val_mem SEGS (mrestrict (w_H W) mem') (spZ regs - 64) 8 (bv_unsigned (getr regs 22)) /\
     rdword (aview SEGS (w_H W) mem') (frame_addr lyc 0 pos + 56) = Some (flag_addr lyc 0 pos) /\
     (exists junk, length junk = 10%nat /\
        garr8 SEGS (mrestrict (w_H W) mem') (frame_addr lyc 0 pos + 32) junk) /\
     range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF (frame_addr lyc 0 pos + 32) 10 /\
     (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - PUT_DEC_STK <= a < spZ regs) ->
        apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
     (forall a, spZ regs - PUT_DEC_STK <= a < spZ regs -> apresent (w_H W) mem' a) /\
     (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - PUT_DEC_STK <= a < spZ regs) ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
     (forall bb m i, In (bb, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
        aview SEGS (w_H W) mem' (bb + i) = aview SEGS (w_H W) memc (bb + i)) /\
     (forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) ->
        ~ (as_errno B <= a < as_errno B + 4) ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
     (forall cid pos' a, In (cid, pos') (frames Sc) ->
        (in_zr a (frame_rng lyc (cid, pos')) \/
         in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b mn
HJc Hra0 Hra4 Hgp Htp G10 G11 G13 Hmn Hal32 Hwlo Hwhi Hfrlen.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : PUT_DEC_STK = 4208) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof HJc as (HARc & Hlyc & _ & _ & _ & Hfrsc & _ & _ & F1c & F2c & F3c & F4c & _ & Hpresc & HST & _).
destruct HST as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hal16 : spZ regs mod 16 = 0).
{ pose proof (Z.div_mod (spZ regs) 32 ltac:(lia)) as D. rewrite Hal32, Z.add_0_r in D.
  replace (spZ regs) with (2 * (spZ regs / 32) * 16) by lia. apply Z_mod_mult. }
destruct (al_const _ _ LAWS lyc Sc W memc mdc HARc) as (Kcell & Kuar & Kgot & Kguar).
rewrite HBcell in Kcell. rewrite HBgot, HBcell in Kgot.
rewrite (palf_got_uar B TLF) in Kguar.
pose proof (palf_uar_img B TLF) as Huarimg. pose proof (palf_uar_al B TLF) as Huaral.
pose proof (pa_obj_img 0%nat ltac:(lia)) as Hob0. pose proof (pa_obj_img 1%nat ltac:(lia)) as Hob1.
pose proof (pa_obj_img 31%nat ltac:(lia)) as Hob31.
remember (Eimg (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (as_uar_cell B)])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (AGE : env_agree 32 (Ereg regs [Z_to_bv 64 SB; Z_to_bv 64 (as_uar_cell B)]) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall m (r : bv 5), Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
by (intros m r Hm; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hm).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
assert (E1 : ew E 1 = getr regs 1) by (exact (EE 1%nat 1%bv eq_refl)).
assert (E2 : ew E 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (E10 : ew E 10 = Z_to_bv 64 b) by (rewrite (EE 10%nat 10%bv eq_refl); exact G10).
assert (E11 : ew E 11 = Z_to_bv 64 p) by (rewrite (EE 11%nat 11%bv eq_refl); exact G11).
assert (E13 : ew E 13 = Z_to_bv 64 mn) by (rewrite (EE 13%nat 13%bv eq_refl); exact G13).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (as_uar_cell B))
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0)))
by (rewrite HE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E242 : ew E (A_OBJ 1) = Z_to_bv 64 (VAL (A_OBJ 1)))
by (rewrite HE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E272 : ew E (A_OBJ 31) = Z_to_bv 64 (VAL (A_OBJ 31)))
by (rewrite HE; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w)
by (intros m w Hm Hw; cbn [base_val]; rewrite Hm; apply unsigned_lit_small; exact Hw).
clear HE.
assert (HS : st_ok_pi SEGS VAL E pd_ss
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_put_dec)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pd_ss. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
    repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
    + cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). apply Hpresc. lia.
    + rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 1)) 0 8 (SOff (A_OBJ 31) 0) (VAL (A_OBJ 31)));
      [cbn [sv_denot]; rewrite E272, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | pose proof (pa_val_range (A_OBJ 31)); zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kgot).
    + rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) E272) by (pose proof (pa_val_range (A_OBJ 31)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 31)) 0 8 (SOff 32 0) SB);
      [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
      rewrite Z.add_0_r. rewrite SB_SHADOW_OFF. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kcell).
    + rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff 33 0) (as_uar_cell B));
      [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Kguar).
    + rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS E _ (as_uar_cell B) 0 4 (SLit 1) 1);
      [cbn [sv_denot]; reflexivity | zside | zside |].
      rewrite Z.add_0_r. exact (val_mem_of_rd32 SEGS (w_H W) memc _ _ Kuar).
  - apply pairwise_disjoint_of_extents.
    unfold stack_region, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
    rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
    rewrite (VB (A_OBJ 1) (VAL (A_OBJ 1)) E242) by (pose proof (pa_val_range (A_OBJ 1)); lia).
    rewrite (VB (A_OBJ 31) (VAL (A_OBJ 31)) E272) by (pose proof (pa_val_range (A_OBJ 31)); lia).
    rewrite (VB 33%nat (as_uar_cell B) E33) by lia.
    cbn [base_val]. rewrite Usp.
    pose proof (palf_sep B TLF) as Hsep. cbn [zseps zseps_from fst snd] in Hsep.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    revert Hsep Hob0 Hob1 Hob31 Huarimg Hceil Hslo Hshi H47 Hstk0 C1 HSTK Hes Hwlo Hwhi.
    clear. intros. repeat match goal with |- _ /\ _ => split end; try exact I; lia.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite Usp, E13, E32, E33, !unsigned_lit_small by (unfold SB in *; lia).
    change (2 ^ 5) with 32. change (2 ^ 3) with 8. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
    revert Hal32 Hmn Huarimg Huaral Hceil Hslo Hshi H47 Hstk0 C1 HSTK Hes Hwlo Hwhi.
    unfold SB. clear. intros.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
unfold cfg_at. change (w64 (BASE + AF_put_dec)) with (Z_to_bv 64 (BASE + AF_put_dec)).
paj_run_shc RUNP RUNC HS HJc.
{ eapply (awr_ok_cons_stack_off _ _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [reflexivity | rewrite Usp; lia | cbn [YP09.r_wlo stack_region]; lia
  | cbn [YP09.r_whi stack_region]; lia |].
  repeat (apply awr_ok_cons_ro; [cbn [YP09.r_wlo YP09.r_whi got_regionP bcell_regionP uar_got_regionP uar_cell_regionP]; lia|]).
  apply awr_ok_nil. }
pose proof HFr as HFr1. pose proof HG as HG1.
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 96 <= a < spZ regs) ->
aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hw.
apply (kept_of_frame E (ss_mem pd_ss) (w_H W) memc (ms_mem ms)
(fun x => spZ regs - 96 <= x < spZ regs) HFr1); [| exact Ha | exact Hw].
intros bb wlo whi aa Hin Hr. unfold pd_ss in Hin.
cbn [ss_mem windows map stack_region got_regionP bcell_regionP uar_got_regionP uar_cell_regionP
YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; cbn [base_val] in Hr;
rewrite ?Usp in Hr; lia|]). destruct Hin. }
prreg HS (1%bv : bv 5) Rra. prreg HS (2%bv : bv 5) Rsp. prreg HS (3%bv : bv 5) Rgp. prreg HS (4%bv : bv 5) Rtp.
pmkst HS.
rewrite (palf_sm0 B TLF).
eapply SRr_bind.
{ lazymatch goal with |- SRr _ _ (mkCfg (mkst (ms_regs ?msX) _ _ _) _) _ =>
eapply (aj_stack_malloc_atS SEGS B LAWS Hsegs errno_low ML SMP 0 ASM0 ltac:(lia) W (ms_regs msX) (ms_mem msX)
STK sp0 FP ly S W0 mem0 md0 own lyc Sc _ k (spZ regs - 96 - sp0) _ HJc) end.
- unfold spZ at 1. rewrite Rsp, Usp, unsigned_lit_small by lia. lia.
- pose proof (Z.div_mod sp0 16 ltac:(lia)) as D0. pose proof (Z.div_mod (spZ regs) 16 ltac:(lia)) as D1.
rewrite Hsp0al, Z.add_0_r in D0. rewrite Hal16, Z.add_0_r in D1.
replace (spZ regs - 96 - sp0) with ((spZ regs / 16 - 6 - sp0 / 16) * 16) by lia. apply Z_mod_mult.
- lia.
- rewrite Hes. lia.
- rewrite Rgp. exact E3.
- rewrite Rtp. exact E4.
- exact Rra.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- pose proof (count_cid_le_length 0 (frames Sc)) as Hcnt.
change (fs_frames 0) with 16384. lia. }
cbv beta.
intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & pos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HJloc & (fS2 & ES2)).
clear Rra Rsp Rgp Rtp.
pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres1 & _).
pose proof (proj1 HJ2) as HAR2.
assert (Hin2f : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
pose proof Hin2f as Hin2.
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR2 Hin2) as (HFal & [HFhi _] & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR2 Hin2) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgP B lyc S2 W mem2 md2 0 pos HAR2 Hin2) as HFimg.
destruct (frame_al64 SEGS B lyc S2 W mem2 md2 0 pos HAR2 Hin2) as (HF64 & _ & _).
change (fs_frame_bytes 0) with 64 in *.
jafter_call_keep_hi HS 512%nat regs2 (mrestrict (w_H W) mem2) HP2 [0%nat] HS2.
match type of HS2 with ?Q -> _ =>
assert (HQ : Q);
[ cbn [ms_mem restrict]; repeat apply Forall_cons; try apply Forall_nil;
split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val stack_region]; rewrite Usp; intros aa Haa;
[ apply (mbyte_of_aview SEGS); apply (proj1 HK); lia
| intros _; apply (apresent_writable SEGS);
apply (proj1 (proj2 (proj2 (proj2 (proj2 HK))))); [lia | lia | apply Hpres1; lia] ]
| specialize (HS2 HQ); clear HQ ] end.
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
pose proof (img_env_havoc_hi E 512%nat (map (getr regs2) CLOB) HEI ltac:(cbv; lia)) as HEI2.
clear HF HFr HG.
prreg HS (10%bv : bv 5) RF. cbn [ms_regs] in RF. rewrite Ha0 in RF. symmetry in RF. unfold w64 in RF.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ => pose (Ea := Ev); change Ev with Ea in HS, HEI2, RF end.
assert (HEI3 : img_env VAL A_LIM (havoc Ea 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]))
by (apply img_env_havoc_hi; [exact HEI2 | cbv; lia]).
pose proof (st_ok_pi_havoc_hi 528 Ea _ _ [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] HS ltac:(cbv; lia)) as HS3.
clear HS HEI2. rename HS3 into HS.
set (Eb := havoc Ea 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)]) in HS, HEI3.
assert (Eb_528 : ew Eb 528 = Z_to_bv 64 FL)
by (unfold Eb; exact (ew_havoc_new Ea 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia))).
assert (Eb_529 : ew Eb 529 = Z_to_bv 64 (SB + F / 8))
by (unfold Eb; exact (ew_havoc_new Ea 528 [Z_to_bv 64 FL; Z_to_bv 64 (SB + F / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia))).
destruct (FFL lyc S2 W mem2 md2 0 pos HAR2 Hin2) as (HFLpres & HFLown & HFLapp & HFLceil).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
assert (Eb_516 : ew Eb 516 = Z_to_bv 64 F)
by (unfold Eb; rewrite ew_havoc_old by lia; exact RF).
assert (Eb_32 : ew Eb 32 = Z_to_bv 64 SB)
by (unfold Eb, Ea; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact E32).
assert (Usp_b : bv_unsigned (ew Eb 2) = spZ regs)
by (unfold Eb, Ea; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact Usp).
assert (HFq : F = 64 * (F / 64)) by (pose proof (Z.div_mod F 64 ltac:(lia)); lia).
assert (HF8 : F / 8 = 8 * (F / 64))
by (rewrite HFq at 1; replace (64 * (F / 64)) with (8 * (F / 64) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
pose proof (YCbq.shadow_addr_bounds F ltac:(lia)) as HSB1.
pose proof (YCbq.shadow_addr_bounds (F + 64) ltac:(lia)) as HSB2.
assert (HSBF : shadow_addr F = SB + F / 8) by (unfold shadow_addr, SB, SHADOW_OFF; lia).
assert (ZS : forall i, 0 <= i < 8 -> aview SEGS (w_H W) mem2 (SB + F / 8 + i) = Some 0).
{ intros i Hi. unfold zero_shadow, shadow_of_addr in Hz. rewrite <- SB_SHADOW_OFF in Hz.
apply Hz. change (64 / 8) with 8. lia. }
pose proof (st_ok_pi_add_fact Eb _ _ 516%nat (HPTR 6) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Eb_516, unsigned_lit_small by lia;
change (2 ^ 6) with 64; repeat split; first [exact HF64 | lia])) as HS3; clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 528%nat (HPTR 0) HS
ltac:(unfold afact_ok, HPTR; cbn [af_lo af_hi af_al2]; rewrite Eb_528, unsigned_lit_small by lia;
rewrite Z.pow_0_r, Z.mod_1_r; repeat split; lia)) as HS3; clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_fact Eb _ _ 529%nat (mkAF (SB + 512) (SB + 2 ^ 44) 3) HS
ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite Eb_529, unsigned_lit_small by (unfold SB; lia);
change (2 ^ 3) with 8; repeat split; try (unfold SB; lia);
rewrite HF8; replace (SB + 8 * (F / 64)) with ((268431360 + F / 64) * 8) by (unfold SB; lia);
apply Z_mod_mult)) as HS3; clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_alias Eb _ _ _ _ HS
(shadow_decl_ok Eb 516 32 529 F SB Eb_516 ltac:(lia) Eb_32 ltac:(rewrite Eb_529; reflexivity))) as HS3;
clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Eb _ _ (YP09.mkRegion (Some 529%nat) 0 8 0 8 [YP09.mkChunk 0 (CVal 8 (SLit 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
rewrite Eb_529, unsigned_lit_small by (unfold SB; lia);
split; [unfold SB; lia|]; split; [unfold SB; lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); rewrite <- HSBF; apply (proj1 (HFSpres o ltac:(change (64 / 8) with 8; lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Eb _ (SB + F / 8) 0 8 (SLit 0) 0);
[reflexivity | unfold SB; zside | zside | rewrite Z.add_0_r; apply val_mem_zero8; exact ZS] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Eb_529, Usp_b; rewrite ?unsigned_lit_small by (unfold SB; lia);
revert HSB1 HSB2 HSBF HF8lo HF8hi HF4096 HFceil Hceil Hslo Hshi H47 Hstk0 C1 HSTK Hes Hwlo Hwhi; unfold SB;
clear; intros; repeat split; try exact I; lia)) as HS3; clear HS; rename HS3 into HS.
pose proof (st_ok_pi_add_region Eb _ _ (YP09.mkRegion (Some 516%nat) 0 64 0 64 [YP09.mkChunk 56 (CVal 8 (SOff 528 0))]) HS eq_refl
ltac:(unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
rewrite Eb_516, unsigned_lit_small by lia;
split; [lia|]; split; [lia|]; split;
[ intros o Ho; apply (apresent_writable SEGS); apply (proj1 (HFpres (F + o) ltac:(lia)))
| apply Forall_cons; [|apply Forall_nil];
apply (chunk_ok_val SEGS Eb _ F 56 8 (SOff 528 0) FL);
[cbn [sv_denot]; rewrite Eb_528, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |
cbn [ms_mem restrict mkst]; replace (F + 56) with (F + 64 - 8) by lia;
exact (val_mem_of_rdword SEGS (w_H W) mem2 _ _ Hflag)] ])
ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
cbn [all_disjoint]; unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite Eb_516, Eb_529, Usp_b; rewrite ?unsigned_lit_small by (unfold SB; lia);
unfold in_app, kLowShadowBeg, kHighMemBeg in HFapp;
revert HFapp HSB1 HSB2 HSBF HF8lo HF8hi HFq HF8 HF4096 HFceil Hceil Hslo Hshi H47 Hstk0 C1 HSTK Hes Hwlo Hwhi; unfold SB;
clear; intros; repeat split; try exact I; lia)) as HS3; clear HS; rename HS3 into HS.
paj_run_to_sh RUNTOP HS HJ2 0x2254.
{ eapply (awr_ok_cons_gen Eb _ _ _ _ _ _ _ _ _ 516%nat F);
  [reflexivity | rewrite Eb_516; apply unsigned_lit_small; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; right; right; right; exists 0, pos;
    split; [left; reflexivity|]; left; unfold in_zr; cbn [fst snd]; fold F; change (fs_frame_bytes 0) with 64; lia |].
  eapply (awr_ok_cons_gen Eb _ _ _ _ _ _ _ _ _ 529%nat (SB + F / 8));
  [reflexivity | rewrite Eb_529; apply unsigned_lit_small; unfold SB; lia
  | cbn [YP09.r_wlo YP09.r_whi]; intros aa Haa; right; right; right; exists 0, pos;
    split; [left; reflexivity|]; right; unfold in_zr; cbn [fst snd]; fold F; rewrite HSBF;
    change (fs_frame_bytes 0) with 64; change (64 / 8) with 8; lia |].
  eapply (awr_ok_cons_stack_off Eb _ _ _ _ _ _ _ _ _ 2%nat (spZ regs - sp0));
  [reflexivity | rewrite Usp_b; lia | cbn [YP09.r_wlo]; lia | cbn [YP09.r_whi]; lia | apply awr_ok_nil]. }
assert (Eb_1 : ew Eb 1 = getr regs 1)
by (unfold Eb, Ea; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact E1).
assert (Eb_3 : ew Eb 3 = w64 (as_gp B))
by (unfold Eb, Ea; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact E3).
assert (Eb_4 : ew Eb 4 = w64 (as_tp B))
by (unfold Eb, Ea; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact E4).
assert (Eb_10 : ew Eb 10 = Z_to_bv 64 b)
by (unfold Eb, Ea; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact E10).
assert (Eb_11 : ew Eb 11 = Z_to_bv 64 p)
by (unfold Eb, Ea; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact E11).
assert (Eb_12 : ew Eb 12 = getr regs 12)
by (unfold Eb, Ea; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact (EE 12%nat 12%bv eq_refl)).
assert (Eb_13 : ew Eb 13 = Z_to_bv 64 mn)
by (unfold Eb, Ea; rewrite ew_havoc_old by lia; rewrite ew_havoc_old by lia; exact E13).
assert (Eb_8 : ew Eb 8 = getr regs 8)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 8%nat 8%bv eq_refl)).
assert (Eb_9 : ew Eb 9 = getr regs 9)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 9%nat 9%bv eq_refl)).
assert (Eb_18 : ew Eb 18 = getr regs 18)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 18%nat 18%bv eq_refl)).
assert (Eb_19 : ew Eb 19 = getr regs 19)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 19%nat 19%bv eq_refl)).
assert (Eb_20 : ew Eb 20 = getr regs 20)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 20%nat 20%bv eq_refl)).
assert (Eb_21 : ew Eb 21 = getr regs 21)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 21%nat 21%bv eq_refl)).
assert (Eb_22 : ew Eb 22 = getr regs 22)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 22%nat 22%bv eq_refl)).
assert (Eb_23 : ew Eb 23 = getr regs 23)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 23%nat 23%bv eq_refl)).
assert (Eb_24 : ew Eb 24 = getr regs 24)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 24%nat 24%bv eq_refl)).
assert (Eb_25 : ew Eb 25 = getr regs 25)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 25%nat 25%bv eq_refl)).
assert (Eb_26 : ew Eb 26 = getr regs 26)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 26%nat 26%bv eq_refl)).
assert (Eb_27 : ew Eb 27 = getr regs 27)
by (unfold Eb, Ea; rewrite !ew_havoc_old by lia; exact (EE 27%nat 27%bv eq_refl)).
assert (Eb_2 : ew Eb 2 = Z_to_bv 64 (spZ regs))
by (rewrite <- Usp_b; symmetry; apply Z_to_bv_bv_unsigned).
clear E1 E2 E3 E4 E10 E11 E13 E32 E241 E242 E272 Usp.
pmkst HS.
apply SRr_ret.
split; [reflexivity|]. exists S2, pos. do 3 eexists.
split; [reflexivity|].
split; [exact HJ2|].
split; [exact Hfrs2|]. split; [exact Eab|]. split; [exact Hnev2|]. split; [exact Hbb2|].
do 28 (split; [first [pd_reg HS | lazymatch goal with |- getr _ 15 = _ =>
let T := fresh "T15" in prreg HS (15%bv : bv 5) T; cbn [ms_regs] in T; rewrite T; clear T;
rewrite Eb_516, unsigned_lit_small by lia;
apply bv_eq; rewrite YO0c.alu64_xori_m1; unfold YO0a.not64; rewrite unsigned_lit_small by lia;
rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); f_equal;
pose proof (Z.add_lnot_diag (F + 32)); lia end] |]).
split; [pd_slot HS (-8) 1%nat Usp_b|].
split; [pd_slot HS (-16) 8%nat Usp_b|].
split; [pd_slot HS (-24) 9%nat Usp_b|].
split; [pd_slot HS (-32) 18%nat Usp_b|].
split; [pd_slot HS (-40) 19%nat Usp_b|].
split; [pd_slot HS (-48) 20%nat Usp_b|].
split; [pd_slot HS (-56) 21%nat Usp_b|].
split; [pd_slot HS (-64) 22%nat Usp_b|].
(* the flag pointer, kept in the frame's last word *)
split.
{ lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ssx (restrict ?Hh ?msx) =>
pose proof (@field_of_region_any sg Ex (ms_mem (restrict Hh msx)) 516%nat _ _ 0 64 0 64 56 8%N (SOff 528 0)
(st_ok_pi_region_nth Ex ssx _ 0%nat _ HS eq_refl)
ltac:(rewrite Eb_516; apply unsigned_lit_small; lia)
ltac:(vm_compute; repeat (first [left; reflexivity | right])) ltac:(cbn; lia)) as VF end.
cbn [ms_mem restrict mkst sv_denot] in VF. rewrite Eb_528, Z.add_0_r in VF.
rewrite Z_to_bv_bv_unsigned in VF. replace (8 * Z.of_N 8) with 64 in VF by reflexivity.
rewrite (unsigned_lit_small FL) in VF by lia. rewrite (Z.mod_small FL) in VF by lia.
apply rdword_of_val_mem; [exact VF | lia]. }
(* the ten bytes of the digit buffer *)
assert (HDpres : forall i, 0 <= i < 10 -> exists w, 0 <= w < 256 /\
aview SEGS (w_H W) (ms_mem ms0) (F + 32 + i) = Some w).
{ intros i Hi.
assert (Hp : apresent (w_H W) (ms_mem ms0) (F + 32 + i)).
{ pose proof (proj1 HJ2) as HAR3.
destruct (al_frames _ _ LAWS lyc S2 W (ms_mem ms0) _ 0 pos HAR3 ltac:(rewrite Hfrs2; left; reflexivity)) as (_ & _ & HP3 & _).
change (fs_frame_bytes 0) with 64 in HP3. apply (proj1 (HP3 (F + 32 + i) ltac:(lia))). }
destruct Hp as (Hh & bb & Hb). exists (bv_unsigned bb).
pose proof (bv_unsigned_in_range 8 bb) as Hr. change (bv_modulus 8) with 256 in Hr.
split; [lia|]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. reflexivity. }
split.
{ destruct (HDpres 0 ltac:(lia)) as (w0 & R0 & A0). destruct (HDpres 1 ltac:(lia)) as (w1 & R1 & A1).
destruct (HDpres 2 ltac:(lia)) as (w2 & R2 & A2). destruct (HDpres 3 ltac:(lia)) as (w3 & R3 & A3).
destruct (HDpres 4 ltac:(lia)) as (w4 & R4 & A4). destruct (HDpres 5 ltac:(lia)) as (w5 & R5 & A5).
destruct (HDpres 6 ltac:(lia)) as (w6 & R6 & A6). destruct (HDpres 7 ltac:(lia)) as (w7 & R7 & A7).
destruct (HDpres 8 ltac:(lia)) as (w8 & R8 & A8). destruct (HDpres 9 ltac:(lia)) as (w9 & R9 & A9).
exists [w0; w1; w2; w3; w4; w5; w6; w7; w8; w9]. split; [reflexivity|].
intros j Hj. cbn [length] in Hj.
assert (Hgen : forall i w, 0 <= i < 10 -> aview SEGS (w_H W) (ms_mem ms0) (F + 32 + i) = Some w ->
0 <= w < 256 -> val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (F + 32 + i) 1 w).
{ intros i w Hi Ha Hw kk Hk. destruct kk as [|kk]; [|cbn in Hk; lia].
destruct (aview_byte SEGS (w_H W) (ms_mem ms0) (F + 32 + i) w Ha) as (bb & Hb & Hv & _).
rewrite Z.add_0_r, Hb. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned.
unfold bv_wrap, YO0f.le_byte. change (bv_modulus 8) with 256.
change (8 * Z.of_nat 0) with 0. change (2 ^ (8 * Z.of_nat 1)) with 256.
rewrite Z.shiftr_0_r, !Z.mod_mod by lia. rewrite <- Hv. rewrite Z.mod_small by lia. reflexivity. }
do 10 (destruct j as [|j]; [cbn [nth Z.of_nat]; split;
[ first [ exact (Hgen 0 w0 ltac:(lia) A0 R0) | exact (Hgen 1 w1 ltac:(lia) A1 R1)
| exact (Hgen 2 w2 ltac:(lia) A2 R2) | exact (Hgen 3 w3 ltac:(lia) A3 R3)
| exact (Hgen 4 w4 ltac:(lia) A4 R4) | exact (Hgen 5 w5 ltac:(lia) A5 R5)
| exact (Hgen 6 w6 ltac:(lia) A6 R6) | exact (Hgen 7 w7 ltac:(lia) A7 R7)
| exact (Hgen 8 w8 ltac:(lia) A8 R8) | exact (Hgen 9 w9 ltac:(lia) A9 R9) ]
| lia] |]). cbn in Hj. lia. }
(* the two shadow bytes of the digit buffer, and the addressability they give *)
assert (SHB : forall od w, od = 4 \/ od = 5 -> (od = 4 -> w = 0) -> (od = 5 -> w = 2) ->
aview SEGS (w_H W) (ms_mem ms0) (SB + F / 8 + od) = Some w).
{ intros od w Hod H4 H5.
lazymatch type of HS with st_ok_pi ?sg _ ?Ex ?ssx (restrict ?Hh ?msx) =>
pose proof (@field_of_region sg Ex (ms_mem (restrict Hh msx)) 529%nat _ _ 0 8 0 8 od 1%N (SLit w) w
(st_ok_pi_region_nth Ex ssx _ 1%nat _ HS eq_refl)
ltac:(rewrite Eb_529; apply unsigned_lit_small; unfold SB; lia)
ltac:(destruct Hod as [-> | ->]; [rewrite (H4 eq_refl) | rewrite (H5 eq_refl)];
vm_compute; repeat (first [left; reflexivity | right]))
ltac:(destruct Hod as [-> | ->]; [rewrite (H4 eq_refl) | rewrite (H5 eq_refl)]; reflexivity)
ltac:(destruct Hod as [-> | ->]; [rewrite (H4 eq_refl) | rewrite (H5 eq_refl)]; cbn; lia)
ltac:(cbn; lia)) as VS end.
cbn [ms_mem restrict mkst] in VS.
apply aview_of_val_mem1; [exact VS | destruct Hod as [-> | ->]; [rewrite (H4 eq_refl) | rewrite (H5 eq_refl)]; lia]. }
assert (HRA : range_addressable (aview SEGS (w_H W) (ms_mem ms0)) SHADOW_OFF (F + 32) 10).
{ intros x Hx. unfold shadow_of_addr. rewrite <- SB_SHADOW_OFF.
destruct (Z_lt_le_dec x (F + 40)) as [Hlt | Hge].
- exists 0. split; [|left; reflexivity].
replace (SB + x / 8) with (SB + F / 8 + 4);
[exact (SHB 4 0 ltac:(left; reflexivity) ltac:(reflexivity) ltac:(discriminate))
| rewrite HF8; replace x with ((8 * (F / 64) + 4) * 8 + (x - (F + 32))) by lia;
rewrite Z.div_add_l by lia; rewrite (Z.div_small (x - (F + 32))) by lia; lia].
- exists 2. split.
+ replace (SB + x / 8) with (SB + F / 8 + 5);
[exact (SHB 5 2 ltac:(right; reflexivity) ltac:(discriminate) ltac:(reflexivity))
| rewrite HF8; replace x with ((8 * (F / 64) + 5) * 8 + (x - (F + 40))) by lia;
rewrite Z.div_add_l by lia; rewrite (Z.div_small (x - (F + 40))) by lia; lia].
+ right. split; [| lia].
replace x with ((x - (F + 40)) + (8 * (F / 64) + 5) * 8) by lia.
rewrite Z_mod_plus_full. rewrite (Z.mod_small (x - (F + 40))) by lia. lia. }
split; [exact HRA|].
(* presence *)
split.
{ intros a Ha Hw Hp. eapply apresent_grows; [exact HG|].
apply (proj1 (proj2 (proj2 (proj2 (proj2 HK))))); [lia | lia |].
eapply apresent_grows; [exact HG1 | exact Hp]. }
split.
{ pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres3 & _).
intros a Ha. apply Hpres3. lia. }
(* everything outside the window, the frame and the frame's shadow is kept *)
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
~ (spZ regs - 96 <= a < spZ regs) -> ~ (F <= a < F + 64) ->
~ (SB + F / 8 <= a < SB + F / 8 + 8) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) mem2 a).
{ intros a Ha Hw Hf Hs.
apply (kept_of_frame Eb _ (w_H W) mem2 (ms_mem ms0)
(fun x => (spZ regs - 96 <= x < spZ regs) \/ (F <= x < F + 64) \/ (SB + F / 8 <= x < SB + F / 8 + 8)) HFr);
[| exact Ha | intros [HH|[HH|HH]]; [exact (Hw HH) | exact (Hf HH) | exact (Hs HH)]].
intros bb wlo whi aa Hin Hr.
cbn [windows map YP09.r_base YP09.r_wlo YP09.r_whi] in Hin.
repeat (destruct Hin as [Eq | Hin]; [injection Eq as <- <- <-; cbn [base_val] in Hr;
rewrite ?Eb_516, ?Eb_529, ?Usp_b in Hr; rewrite ?unsigned_lit_small in Hr by (unfold SB; lia);
first [right; left; lia | right; right; lia | left; lia] |]). destruct Hin. }
(* separation of the new frame and its shadow from the caller's picture *)
assert (HFsh : forall a, SB + F / 8 <= a < SB + F / 8 + 8 -> kLowMemEnd <= a < kHighShadowEnd).
{ intros a Ha. rewrite <- HSBF in Ha.
pose proof (shadow_range_end F 64 ltac:(lia)) as Hre. change (64 / 8) with 8 in Hre. unfold kLowMemEnd, kHighShadowEnd in *. lia. }
assert (HBLK : forall bb m i, In (bb, m) (ablocks B lyc Sc) -> 0 <= i < req_size m ->
alloc_ceiling > bb + i /\ ~ (F <= bb + i < F + 64) /\ ~ (SB + F / 8 <= bb + i < SB + F / 8 + 8)).
{ intros bb m i Hin Hi.
assert (Hinb : In (bb, m) (ablocks B lyc S2)) by (rewrite Eab; exact Hin).
destruct (al_blocks _ _ LAWS lyc S2 W mem2 md2 bb m HAR2 Hinb) as (_ & H4096 & Hce & Happ & _).
pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 bb m 0 pos HAR2 Hinb Hin2f) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd. fold F in Hd.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ.
pose proof (HFsh (SB + F / 8)) as Hsh0.
split; [lia|]. split; [lia|]. intros Hx. pose proof (HFsh (bb + i) Hx). unfold kLowMemEnd, kHighShadowEnd in *.
unfold SB in *. lia. }
assert (HIMG : forall a, in_img SEGS a ->
~ (spZ regs - 96 <= a < spZ regs) /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8)).
{ intros a Hi. pose proof (pa_img_range a Hi) as Hr. pose proof (Hsegs a Hi) as Hlow.
split; [unfold kLowMemEnd in *; lia|]. split; [lia|].
intros Hx. pose proof (HFsh a Hx). unfold kLowMemEnd in *. lia. }
assert (HFRM : forall cid pos' a, In (cid, pos') (frames Sc) ->
(in_zr a (frame_rng lyc (cid, pos')) \/ in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
~ (spZ regs - 96 <= a < spZ regs) /\ ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8)).
{ intros cid pos' a Hin Hr.
assert (HinS2 : In (cid, pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin).
destruct (frame_zone SEGS B LAWS lyc S2 W mem2 md2 cid pos' a HAR2 HinS2 Hr) as (Hceil' & _).
split; [lia|].
assert (Hdj : forall Hr2 : (in_zr a (frame_rng lyc (0, pos)) \/
in_zr a (shadow_addr (frame_addr lyc 0 pos), fs_frame_bytes 0 / 8)), False).
{ intros Hr2. apply in_split in Hin as (l1 & l2 & El).
apply (frames_zone_disj SEGS B LAWS lyc S2 W mem2 md2 (0, pos) (cid, pos') [] l1 l2 a HAR2);
[rewrite Hfrs2, El; reflexivity | cbn [fst snd]; exact Hr2 | cbn [fst snd]; exact Hr]. }
split; [intros Hx; apply Hdj; left; unfold frame_rng, in_zr; cbn [fst snd]; fold F;
change (fs_frame_bytes 0) with 64; lia
| intros Hx; apply Hdj; right; unfold in_zr; cbn [fst snd]; fold F; rewrite HSBF;
change (fs_frame_bytes 0) with 64; change (64 / 8) with 8; lia]. }
split.
{ intros a Ha Hw.
rewrite (KEEP2 a ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros Hx; pose proof (HFsh a Hx); unfold kHighShadowEnd in *; lia)).
rewrite (proj1 HK a ltac:(lia) ltac:(lia)). apply KEEP1; [lia | lia]. }
split.
{ intros bb m i Hin Hi. destruct (HBLK bb m i Hin Hi) as (Hc & Hf & Hs).
destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb m HARc Hin) as (_ & H4096 & _ & _ & _).
rewrite (KEEP2 (bb + i) ltac:(lia) ltac:(lia) Hf Hs).
rewrite (proj1 (proj2 HK) bb m i Hin Hi ltac:(intros [])).
apply KEEP1; [lia | lia]. }
split.
{ intros a Hi Hns He. destruct (HIMG a Hi) as (Hw & Hf & Hs).
pose proof (Hsegs a Hi) as Hlow. pose proof (pa_img_range a Hi) as Hr.
rewrite (KEEP2 a ltac:(unfold kLowMemEnd in *; lia) Hw Hf Hs).
rewrite (proj1 (proj2 (proj2 HK)) a Hi Hns He).
apply KEEP1; [unfold kLowMemEnd in *; lia | lia]. }
{ intros cid pos' a Hin Hr. destruct (HFRM cid pos' a Hin Hr) as (Hw & Hf & Hs).
destruct (frame_zone SEGS B LAWS lyc Sc W memc mdc cid pos' a HARc Hin Hr) as (Hceil' & Hcase).
assert (Haz : 0 <= a < 2 ^ 64).
{ destruct Hcase as [(Hr1 & Happ') | Hr2];
[ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ'; lia
| unfold kLowMemEnd, kHighShadowEnd in Hr2; lia ]. }
rewrite (KEEP2 a Haz Hw Hf Hs).
rewrite (proj1 (proj2 (proj2 (proj2 HK))) cid pos' a Hin Hr ltac:(intros [])).
apply KEEP1; [exact Haz | lia]. }
Qed.

(* ---- the digit loop ---- *)
(* the bytes a run left alone: its only writable window is the one digit byte at atom 5 *)
Ltac dl_keep HFrh F5h Hn :=
lazymatch type of HFrh with
| frame_of ?Ex ?rsx (mrestrict ?H ?m1) (mrestrict _ ?m2) =>
  lazymatch type of F5h with
  | bv_unsigned (ew _ 5) = ?v =>
    assert (Hn : forall a, 0 <= a < 2 ^ 64 -> ~ (v <= a < v + 1) ->
              aview SEGS H m2 a = aview SEGS H m1 a);
    [ apply (kept_of_frame Ex rsx H m1 m2 (fun a => v <= a < v + 1) HFrh);
      intros bb wlo whi aa Hin Hr;
      let w := eval vm_compute in (windows rsx) in change (windows rsx) with w in Hin;
      destruct Hin as [Hq | []]; injection Hq as <- <- <-;
      cbn [base_val] in Hr; rewrite F5h in Hr; lia
    | ]
  end
end.
(* the digit byte the state's one chunk records *)
Ltac dl_vd HSh F5h F21h EXh Hn :=
lazymatch type of HSh with
| st_ok_pi _ _ ?Ex ?ssx (restrict ?H ?msx) =>
  lazymatch type of F5h with
  | bv_unsigned (ew _ 5) = ?v =>
    pose proof (@field_of_region_any SEGS Ex _ 5%nat v _ 0 1 0 1 0 1%N _
      (st_ok_pi_region_nth Ex ssx _ 0%nat _ HSh eq_refl) F5h
      ltac:(left; reflexivity) ltac:(cbn; lia)) as Hn;
    cbn [restrict ms_mem] in Hn; rewrite Z.add_0_r in Hn;
    change (N.to_nat 1) with 1%nat in Hn;
    rewrite dl_unsig_U, (dl_U_dig _ _ _ F21h EXh) in Hn;
    change (8 * Z.of_N 1) with 8 in Hn; change (2 ^ 8) with 256 in Hn;
    rewrite Z.mod_small in Hn by lia
  end
end.


Lemma pd_dloop : forall (f : nat) (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (St : astate)
  (W0 : world SEGS) (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z))
  (lyc : alayout) (Sc : astate) (W : world SEGS) (memc : word -> option byte) (mdc : Model) (k : Z)
  (regs : bvmap 5 word) (pos D i x : Z) (xw : word) (pre post : list Z),
  (1 <= f)%nat -> x < 10 ^ Z.of_nat f ->
  bv_unsigned xw mod 2 ^ 32 = x -> (bv_unsigned xw < 2 ^ 32 \/ 10 <= x) ->
  ajournal SEGS B STK sp0 FP ly St W0 mem0 md0 ((0, pos) :: own) lyc Sc W memc mdc k ->
  In (0, pos) (frames Sc) -> D = frame_addr lyc 0 pos + 32 ->
  i = Z.of_nat (length pre) ->
  (length (put_dec.ds_lsb f x) <= length post)%nat -> (length pre + length post = 10)%nat ->
  garr8 SEGS (mrestrict (w_H W) memc) D (pre ++ post) ->
  range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF D 10 ->
  getr regs 5 = w64 (D + i) -> getr regs 6 = w64 10 ->
  getr regs 7 = w64 14757395259826634752 -> getr regs 11 = w64 (D + i) ->
  getr regs 16 = w64 i -> getr regs 17 = w64 i -> getr regs 21 = xw ->
  getr regs 22 = w64 SB -> getr regs 28 = w64 9 ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x2254)) memc (seg_rom SEGS)) mdc)
    (fun W' c' => W' = W /\ exists regs' mem' md',
       c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x22b0)) mem' (seg_rom SEGS)) md' /\
       ajournal SEGS B STK sp0 FP ly St W0 mem0 md0 ((0, pos) :: own) lyc Sc W mem' md' k /\
       garr8 SEGS (mrestrict (w_H W) mem') D
         (pre ++ map bv_unsigned (put_dec.ds_lsb f x) ++ skipn (length (put_dec.ds_lsb f x)) post) /\
       (forall a, 0 <= a < 2 ^ 64 -> ~ (D <= a < D + 10) ->
          aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
       (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a) /\
       range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF D 10 /\
       getr regs' 5 = w64 (D + i + Z.of_nat (length (put_dec.ds_lsb f x))) /\
       getr regs' 11 = w64 (D + i + Z.of_nat (length (put_dec.ds_lsb f x))) /\
       getr regs' 16 = w64 (i + Z.of_nat (length (put_dec.ds_lsb f x))) /\
       getr regs' 17 = w64 (i + Z.of_nat (length (put_dec.ds_lsb f x))) /\
       getr regs' 21 = w64 (x / 10 ^ Z.of_nat (length (put_dec.ds_lsb f x))) /\
       getr regs' 6 = w64 10 /\ getr regs' 7 = w64 14757395259826634752 /\ getr regs' 28 = w64 9 /\
       (forall r, In r DL_KEPT -> getr regs' r = getr regs r)).
Proof.
induction f as [|f IH];
intros STK sp0 FP ly St W0 mem0 md0 own lyc Sc W memc mdc k regs pos D i x xw pre post
  Hf Hx EX HX HJ Hfr HD Hi Hlen Hsum GIN HRA R5 R6 R7 R11 R16 R17 R21 R22 R28; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof (u64_range xw) as Hu.
assert (Hx0 : 0 <= x < 2 ^ 32) by (rewrite <- EX; apply Z.mod_pos_bound; lia).
pose proof (Z.mod_pos_bound x 10 ltac:(lia)) as Hmod.
assert (Hdiv : 0 <= x / 10 <= x) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
assert (HFB : fs_frame_bytes 0 = 64) by reflexivity.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 0 pos HAR Hfr) as (HF0 & HFc & HFapp).
rewrite HFB in HFc, HFapp.
assert (HL1 : (1 <= length (put_dec.ds_lsb (S f) x))%nat)
  by (cbn [put_dec.ds_lsb]; cbn [length]; lia).
assert (Hpost1 : (1 <= length post)%nat) by lia.
destruct post as [|y post']; [cbn [length] in Hpost1; lia|].
cbn [length] in Hsum.
assert (Hi0 : 0 <= i <= 9) by lia.
assert (HDlo : 4096 + 32 <= D) by lia.
assert (HDhi : D + 10 <= frame_addr lyc 0 pos + 64) by lia.
assert (HD47 : 0 <= D + i < 2 ^ 47) by lia.
(* shadow bytes of [D, D+10) are never the byte this iteration stores *)
assert (HSH : forall a, D <= a < D + 10 ->
  0 <= SHADOW_OFF + a / 8 < 2 ^ 64 /\ SHADOW_OFF + a / 8 <> D + i).
{ intros a Ha. pose proof (shadow_addr_bounds a ltac:(unfold kHighMemEnd; lia)) as Hs.
  unfold shadow_addr, kLowMemEnd, kHighShadowEnd in Hs.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
  unfold SHADOW_OFF in *. split; lia. }
(* --- the valuation at the loop head ------------------------------------------------------------ *)
remember (Eimg (Ereg regs [])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EL : forall n, (n < 32)%nat -> ew E n = ew (Ereg regs []) n)
  by (intros n Hn; subst E; apply Eimg_low; unfold A_TEXT; lia).
assert (HAE : env_agree 32 (Ereg regs []) E)
  by (split; [intros n Hn; apply EL; lia | subst E; reflexivity]).
assert (E5 : ew E 5 = w64 (D + i))
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 5 5%bv eq_refl); exact R5).
assert (E6 : ew E 6 = w64 10)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 6 6%bv eq_refl); exact R6).
assert (E7 : ew E 7 = w64 14757395259826634752)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 7 7%bv eq_refl); exact R7).
assert (E11 : ew E 11 = w64 (D + i))
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact R11).
assert (E16 : ew E 16 = w64 i)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 16 16%bv eq_refl); exact R16).
assert (E17 : ew E 17 = w64 i)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 17 17%bv eq_refl); exact R17).
assert (E21 : ew E 21 = xw)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 21 21%bv eq_refl); exact R21).
assert (E22 : ew E 22 = w64 SB)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 22 22%bv eq_refl); exact R22).
assert (E28 : ew E 28 = w64 9)
  by (rewrite EL by lia; rewrite (ew_Ereg_nat regs _ 28 28%bv eq_refl); exact R28).
assert (E5u : bv_unsigned (ew E 5) = D + i) by (rewrite E5; apply unsigned_lit_small; lia).
assert (E11u : bv_unsigned (ew E 11) = D + i) by (rewrite E11; apply unsigned_lit_small; lia).
assert (E16u : bv_unsigned (ew E 16) = i) by (rewrite E16; apply unsigned_lit_small; lia).
assert (E22u : bv_unsigned (ew E 22) = SB) by (rewrite E22; apply unsigned_lit_small; unfold SB; lia).
assert (UBx : U E dl_Bx = SHADOW_OFF)
  by (unfold dl_Bx; rewrite U_SOff, E22u, Z.add_0_r, zcanon_id by (unfold SB, M64; lia); reflexivity).
assert (U5 : U E (SOff 5 0) = D + i)
  by (rewrite U_SOff, E5u, Z.add_0_r; apply zcanon_id; unfold M64; lia).
assert (U11 : U E (SOff 11 0) = D + i)
  by (rewrite U_SOff, E11u, Z.add_0_r; apply zcanon_id; unfold M64; lia).
(* --- the state at the loop head ---------------------------------------------------------------- *)
destruct (al_frames SEGS B LAWS lyc Sc W memc mdc 0 pos HAR Hfr) as (_ & _ & Hfpres & _).
rewrite HFB in Hfpres.
assert (HS : st_ok_pi SEGS VAL E ss_dl
  (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x2254)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_dl. apply pa_entry_st_ok_full.
  - unfold dl_sr.
    apply regs_ok_pin; [|discriminate|cbn [sv_denot]; exact R28].
    apply regs_ok_pin; [|discriminate|cbn [sv_denot]; exact R7].
    apply regs_ok_pin; [|discriminate|cbn [sv_denot]; exact R6].
    rewrite HE. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold dl_regions. apply Forall_cons; [|apply Forall_nil]. unfold region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E5u. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). exact (proj1 (Hfpres (D + i + o) ltac:(lia))).
  - apply pairwise_disjoint_of_extents. cbn. repeat constructor.
  - split; [|split; [exact I | exact I]].
    cbn [dl_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite E5u, E11u, E16u, E22u. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SB; lia. }
assert (SHOK : sh_ok SEGS dl_Bx dl_SH E (mrestrict (w_H W) memc)).
{ unfold dl_SH. apply Forall_cons; [|apply Forall_nil].
  exact (shent_app_of_frame SEGS B LAWS lyc Sc W memc mdc E dl_Bx 5 (D + i) 0 pos 0 1 _
           HAR Hfr UBx U5 ltac:(lia) ltac:(lia) ltac:(lia)). }
(* --- run the body: the UBSan trap is not taken, the shadow check is an obligation --------------- *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite U11, UBx. rewrite <- (aview_rd_of SEGS).
  eapply range_addressable_sub; [exact HRA | lia | lia]. }
{ lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
    let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
  eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 5%nat (D + i));
  [ reflexivity
  | cbn [ew ewset Nat.eqb]; exact E5u
  | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
    right; right; right; exists 0, pos; split; [left; reflexivity|];
    left; unfold in_zr; cbn [fst snd]; lia
  | apply awr_ok_nil ]. }
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ => remember Ex as E2 eqn:HE2 end.
assert (OLD : forall n, (n < 512)%nat -> ew E2 n = ew E n)
  by (intros n Hn; rewrite HE2, !ew_ewset_other by lia; reflexivity).
assert (F21 : ew E2 21 = xw) by (rewrite OLD by lia; exact E21).
assert (F17 : ew E2 17 = w64 i) by (rewrite OLD by lia; exact E17).
assert (F5u : bv_unsigned (ew E2 5) = D + i) by (rewrite OLD by lia; exact E5u).
(* what the store left alone *)
dl_keep HFr E5u KEEP1.
assert (HPR1 : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Hp; exact (apresent_grows (w_H W) memc (ms_mem ms) a HG Hp)).
clear HF HFr HG.
(* the digit buffer, split at the byte this iteration overwrites *)
pose proof (proj1 (garr8_app SEGS (mrestrict (w_H W) memc) D pre (y :: post')) GIN) as [GPpre GPpost].
rewrite <- Hi in GPpost.
pose proof (proj1 (garr8_app SEGS (mrestrict (w_H W) memc) (D + i) [y] post') GPpost) as [_ GPtail].
change (Z.of_nat (length [y])) with 1 in GPtail.
assert (Hdg : bv_unsigned (dg (x mod 10)) = 48 + x mod 10) by (apply dl_dg; lia).
(* --- the loop test ----------------------------------------------------------------------------- *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* 9 <u s5 : another digit *)
  rewrite branch_ltu_U, (dl_ltu9 E2 xw x F21 EX HX) in Hc.
  assert (Hge : 10 <= x) by (destruct (Z.leb_spec 10 x); [lia | discriminate]).
  assert (Hds : put_dec.ds_lsb (S f) x = dg (x mod 10) :: put_dec.ds_lsb f (x / 10))
    by (cbn [put_dec.ds_lsb]; rewrite (proj2 (Z.ltb_ge x 10) ltac:(lia)); reflexivity).
  assert (Hf1 : (1 <= f)%nat).
  { destruct f; [|lia]. exfalso. change (10 ^ Z.of_nat 1) with 10 in Hx. lia. }
  assert (Hxf : x / 10 < 10 ^ Z.of_nat f).
  { apply Z.div_lt_upper_bound; [lia|].
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hx by lia. lia. }
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x2254.
  { lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 5%nat (D + i));
    [ reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite OLD by lia; exact E5u
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
      right; right; right; exists 0, pos; split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; lia
    | apply awr_ok_nil ]. }
  dl_keep HFr F5u KEEP2.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (D + i <= a < D + i + 1) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
    by (intros a Ha Hn; rewrite (KEEP2 a Ha Hn); apply KEEP1; [lia | exact Hn]).
  assert (HPR : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a)
    by (intros a Hp; exact (apresent_grows (w_H W) (ms_mem ms) (ms_mem ms0) a HG (HPR1 a Hp))).
  dl_vd HS F5u F21 EX VD.
  assert (HRA2 : range_addressable (aview SEGS (w_H W) (ms_mem ms0)) SHADOW_OFF D 10).
  { eapply (range_addressable_agree (aview SEGS (w_H W) memc) (aview SEGS (w_H W) (ms_mem ms0)));
      [|exact HRA].
    intros a Ha. unfold shadow_of_addr. destruct (HSH a Ha) as [Hb Hne]. apply KEEP; lia. }
  assert (GP2 : garr8 SEGS (mrestrict (w_H W) (ms_mem ms0)) D (pre ++ (48 + x mod 10) :: post')).
  { apply (proj2 (garr8_app SEGS (mrestrict (w_H W) (ms_mem ms0)) D pre ((48 + x mod 10) :: post'))).
    split.
    - apply (garr8_frame SEGS (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms0)) D pre GPpre).
      intros a Ha. rewrite <- Hi in Ha. apply (mbyte_of_aview SEGS). apply KEEP; lia.
    - rewrite <- Hi.
      apply (proj2 (garr8_app SEGS (mrestrict (w_H W) (ms_mem ms0)) (D + i) [48 + x mod 10] post')).
      split.
      + apply (dl_garr8_one SEGS (mrestrict (w_H W) (ms_mem ms0)) (D + i) (48 + x mod 10) VD
                 ltac:(lia)).
      + change (Z.of_nat (length [48 + x mod 10])) with 1.
        apply (garr8_frame SEGS (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms0))
                 (D + i + 1) post' GPtail).
        intros a Ha. apply (mbyte_of_aview SEGS). apply KEEP; lia. }
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DL_KEPT HS
                ltac:(rewrite HE2; env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (5%bv : bv 5) N5. prreg HS (11%bv : bv 5) N11.
  prreg HS (16%bv : bv 5) N16. dl_reg HS (17%bv : bv 5) N17.
  dl_reg HS (21%bv : bv 5) N21. prreg HS (6%bv : bv 5) N6.
  prreg HS (7%bv : bv 5) N7. prreg HS (28%bv : bv 5) N28.
  rewrite (OLD 5%nat ltac:(lia)), E5u in N5. rewrite (OLD 11%nat ltac:(lia)), E11u in N11.
  rewrite (OLD 16%nat ltac:(lia)), E16u in N16.
  rewrite (denot_lit_U E2 (SAluw ALU_ADD (SOff 17 0) (SLit 1))), (dl_U_inc E2 i F17 ltac:(lia)) in N17.
  rewrite (denot_lit_U E2 (SAlu ALU_SRL
            (SMd M_MULHU (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 14757395259826634752)) (SLit 35))),
          (dl_U_q E2 xw x F21 EX) in N21.
  pmkst HS.
  eapply SRr_mono.
  { eapply (IH STK sp0 FP ly St W0 mem0 md0 own lyc Sc W _ _ k _ pos D (i + 1) (x / 10)
             (w64 (x / 10)) (pre ++ [48 + x mod 10]) post').
    - exact Hf1.
    - exact Hxf.
    - rewrite unsigned_lit_small by lia. apply Z.mod_small. lia.
    - left. rewrite unsigned_lit_small by lia. lia.
    - exact HJ.
    - exact Hfr.
    - exact HD.
    - rewrite length_app. cbn [length]. lia.
    - rewrite Hds in Hlen. cbn [length] in Hlen. lia.
    - rewrite length_app. cbn [length]. lia.
    - cbn [ms_mem]. rewrite <- app_assoc. cbn [app]. exact GP2.
    - cbn [ms_mem]. exact HRA2.
    - cbn [ms_regs]. rewrite N5. unfold w64. f_equal; lia.
    - cbn [ms_regs]. rewrite N6. reflexivity.
    - cbn [ms_regs]. rewrite N7. reflexivity.
    - cbn [ms_regs]. rewrite N11. unfold w64. f_equal; lia.
    - cbn [ms_regs]. rewrite N16. unfold w64. f_equal; lia.
    - cbn [ms_regs]. rewrite N17. reflexivity.
    - cbn [ms_regs]. rewrite N21. reflexivity.
    - cbn [ms_regs]. rewrite (HK 22%bv ltac:(cbv; tauto)). exact R22.
    - cbn [ms_regs]. rewrite N28. reflexivity. }
  cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & GP3 & KEEP3 & HPR3 & HRA3 &
    M5 & M11 & M16 & M17 & M21 & M6 & M7 & M28 & MK).
  rewrite Hds. cbn [length map].
  assert (HLq : (1 <= length (put_dec.ds_lsb f (x / 10)))%nat)
    by (destruct f; [lia|]; cbn [put_dec.ds_lsb]; cbn [length]; lia).
  split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ3|].
  split.
  { rewrite <- app_assoc in GP3. cbn [app] in GP3. rewrite Hdg. exact GP3. }
  split.
  { intros a Ha Hn. rewrite (KEEP3 a Ha Hn). apply KEEP; lia. }
  split.
  { intros a Hp. apply HPR3. exact (HPR a Hp). }
  split; [exact HRA3|].
  rewrite Nat2Z.inj_succ.
  split. { rewrite M5. unfold w64. f_equal; lia. }
  split. { rewrite M11. unfold w64. f_equal; lia. }
  split. { rewrite M16. unfold w64. f_equal; lia. }
  split. { rewrite M17. unfold w64. f_equal; lia. }
  split.
  { rewrite M21. unfold w64. f_equal.
    rewrite Z.pow_succ_r by lia. rewrite Z.div_div by lia. reflexivity. }
  split; [exact M6|]. split; [exact M7|]. split; [exact M28|].
  intros r Hr. rewrite (MK r Hr). cbn [ms_regs]. exact (HK r Hr).
- (* s5 <=u 9 : the last digit *)
  rewrite branch_ltu_U, (dl_ltu9 E2 xw x F21 EX HX) in Hc.
  assert (Hlt : x < 10) by (destruct (Z.leb_spec 10 x); [discriminate | lia]).
  assert (Hds : put_dec.ds_lsb (S f) x = [dg (x mod 10)])
    by (cbn [put_dec.ds_lsb]; rewrite (proj2 (Z.ltb_lt x 10) ltac:(lia)); reflexivity).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x22b0.
  { lazymatch goal with |- awr_ok ?Ex ?rsx ?stkx ?spx ?fpx ?b0x ?bcx ?lyx ?ownx =>
      let rs' := eval vm_compute in rsx in change (awr_ok Ex rs' stkx spx fpx b0x bcx lyx ownx) end;
    eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 5%nat (D + i));
    [ reflexivity
    | cbn [ew ewset Nat.eqb]; rewrite OLD by lia; exact E5u
    | cbn [YP09.r_wlo YP09.r_whi]; intros a Ha;
      right; right; right; exists 0, pos; split; [left; reflexivity|];
      left; unfold in_zr; cbn [fst snd]; lia
    | apply awr_ok_nil ]. }
  dl_keep HFr F5u KEEP2.
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (D + i <= a < D + i + 1) ->
    aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
    by (intros a Ha Hn; rewrite (KEEP2 a Ha Hn); apply KEEP1; [lia | exact Hn]).
  assert (HPR : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a)
    by (intros a Hp; exact (apresent_grows (w_H W) (ms_mem ms) (ms_mem ms0) a HG (HPR1 a Hp))).
  dl_vd HS F5u F21 EX VD.
  assert (HRA2 : range_addressable (aview SEGS (w_H W) (ms_mem ms0)) SHADOW_OFF D 10).
  { eapply (range_addressable_agree (aview SEGS (w_H W) memc) (aview SEGS (w_H W) (ms_mem ms0)));
      [|exact HRA].
    intros a Ha. unfold shadow_of_addr. destruct (HSH a Ha) as [Hb Hne]. apply KEEP; lia. }
  assert (GP2 : garr8 SEGS (mrestrict (w_H W) (ms_mem ms0)) D (pre ++ (48 + x mod 10) :: post')).
  { apply (proj2 (garr8_app SEGS (mrestrict (w_H W) (ms_mem ms0)) D pre ((48 + x mod 10) :: post'))).
    split.
    - apply (garr8_frame SEGS (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms0)) D pre GPpre).
      intros a Ha. rewrite <- Hi in Ha. apply (mbyte_of_aview SEGS). apply KEEP; lia.
    - rewrite <- Hi.
      apply (proj2 (garr8_app SEGS (mrestrict (w_H W) (ms_mem ms0)) (D + i) [48 + x mod 10] post')).
      split.
      + apply (dl_garr8_one SEGS (mrestrict (w_H W) (ms_mem ms0)) (D + i) (48 + x mod 10) VD
                 ltac:(lia)).
      + change (Z.of_nat (length [48 + x mod 10])) with 1.
        apply (garr8_frame SEGS (mrestrict (w_H W) memc) (mrestrict (w_H W) (ms_mem ms0))
                 (D + i + 1) post' GPtail).
        intros a Ha. apply (mbyte_of_aview SEGS). apply KEEP; lia. }
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ DL_KEPT HS
                ltac:(rewrite HE2; env_agree_chain HAE) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  prreg HS (5%bv : bv 5) N5. prreg HS (11%bv : bv 5) N11.
  prreg HS (16%bv : bv 5) N16. dl_reg HS (17%bv : bv 5) N17.
  dl_reg HS (21%bv : bv 5) N21. prreg HS (6%bv : bv 5) N6.
  prreg HS (7%bv : bv 5) N7. prreg HS (28%bv : bv 5) N28.
  rewrite (OLD 5%nat ltac:(lia)), E5u in N5. rewrite (OLD 11%nat ltac:(lia)), E11u in N11.
  rewrite (OLD 16%nat ltac:(lia)), E16u in N16.
  rewrite (denot_lit_U E2 (SAluw ALU_ADD (SOff 17 0) (SLit 1))), (dl_U_inc E2 i F17 ltac:(lia)) in N17.
  rewrite (denot_lit_U E2 (SAlu ALU_SRL
            (SMd M_MULHU (SAlu ALU_SLL (SOff 21 0) (SLit 32)) (SLit 14757395259826634752)) (SLit 35))),
          (dl_U_q E2 xw x F21 EX) in N21.
  pmkst HS.
  apply SRr_ret. rewrite Hds. cbn [length map skipn].
  split; [reflexivity|].
  lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ (ms_mem ?msx) _) ?mdx] =>
    exists (ms_regs msx), (ms_mem msx), mdx end.
  split; [reflexivity|]. split; [exact HJ|].
  split. { cbn [ms_mem]. rewrite Hdg. exact GP2. }
  split. { cbn [ms_mem]. intros a Ha Hn. apply KEEP; lia. }
  split. { cbn [ms_mem]. exact HPR. }
  split. { cbn [ms_mem]. exact HRA2. }
  cbn [ms_regs].
  split. { rewrite N5. unfold w64. f_equal; lia. }
  split. { rewrite N11. unfold w64. f_equal; lia. }
  split. { rewrite N16. unfold w64. f_equal; lia. }
  split. { rewrite N17. unfold w64. f_equal; lia. }
  split. { rewrite N21. unfold w64. f_equal; change (10 ^ Z.of_nat 1) with 10; reflexivity. }
  split. { rewrite N6. reflexivity. }
  split. { rewrite N7. reflexivity. }
  split. { rewrite N28. reflexivity. }
  exact HK.
Qed.

(* ---- the pad loop ---- *)
(* ------------------------------------------------------------------ *)
(* The symbolic states of the segment.                                  *)
(* ------------------------------------------------------------------ *)

(* s6 holds the shadow base in this build. *)
Definition PL_Bx : sv := SOff 22 0.
(* The registers the segment never writes: ra, sp, gp, tp, s0, s1, a0, a2, a3, a4, a5, s2 .. s11, t4, t5, t6.
   (t0 = 5, t1 = 6, t2 = 7, a1 = 11, a6 = 16, a7 = 17 and t3 = 28 do change.) *)
Definition PL_KEPT : list (bv 5) :=
[1; 2; 3; 4; 8; 9; 10; 12; 13; 14; 15; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 29; 30; 31]%bv.
(* The single byte the loop body stores, based at t0's atom. *)
Definition pl_store_region : YP09.region := YP09.mkRegion (Some 5%nat) 0 1 0 1 [].
Definition ss_pl_entry : sstate := mkSS 0x22b0 sr_atoms [] None (mkFacts [] [] []).
Definition ss_pl_loop : sstate :=
mkSS 0x22c4 (sr_set sr_atoms 6%bv (SLit 48)) [pl_store_region] None
(mkFacts [(5%nat, PTR 0); (11%nat, PTR 0); (22%nat, mkAF SB SB 0)] [] []).
(* A reversed shent: it covers the store window for sh_static_ok, and its range_addressable half is vacuous. *)
Definition PL_SH : list shent := [mkSHE 5 1 0].

(* ------------------------------------------------------------------ *)
(* Small helpers.                                                       *)
(* ------------------------------------------------------------------ *)

Lemma pl_denot_U : forall E (e : sv) v, U E e = v -> 0 <= v < 2 ^ 64 -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H Hv. rewrite <- H. unfold U. rewrite Z_to_bv_bv_unsigned. reflexivity. Qed.

Lemma pl_denot_off : forall E n v c, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = Z_to_bv 64 (v + c).
Proof. intros E n v c Hn Hv Hc. apply pl_denot_U; [apply U_atom_off; assumption | exact Hc]. Qed.

(* prreg, but without prreg_norm: it keeps the  sv_denot E <sv>  shape the rewrites below need. *)
Ltac pl_rreg HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
  pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
  let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
  cbn [ms_regs restrict mkst] in Hr
end.

(* a7 := ((s4 << 32) >>u 32) - a6, the zero-extension of the 32-bit minimum width less the digit count. *)
Lemma pl_sub32 : forall E (mn nd : Z), ew E 20 = Z_to_bv 64 mn -> ew E 16 = Z_to_bv 64 nd ->
0 <= nd -> nd <= mn -> mn <= 10 ->
sv_denot E (SAlu ALU_SUB (SAlu ALU_SRL (SAlu ALU_SLL (SOff 20 0) (SLit 32)) (SLit 32)) (SOff 16 0))
= Z_to_bv 64 (mn - nd).
Proof.
intros E mn nd H20 H16 H0 Hle Hmn. apply pl_denot_U; [|lia].
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom E 16 nd H16) by lia.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (zcanon_id 32) by (unfold M64; lia).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SLit, (zcanon_id 32) by (unfold M64; lia).
rewrite (U_atom E 20 mn H20) by lia.
change (Z.land 32 63) with 32.
rewrite Z.shiftl_mul_pow2 by lia. rewrite (zcanon_id (mn * 2 ^ 32)) by (unfold M64; lia).
rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by lia.
rewrite (zcanon_id mn) by (unfold M64; lia). apply zcanon_id. unfold M64. lia.
Qed.

Lemma pl_val_mem1 : forall (H : word -> bool) (mem : word -> option byte) (a v : Z),
aview SEGS H mem a = Some v -> val_mem SEGS (mrestrict H mem) a 1 v.
Proof.
intros H mem a v Hz j Hj. assert (Hj0 : j = 0%nat) by lia. subst j.
destruct (aview_byte SEGS H mem (a + Z.of_nat 0) v ltac:(rewrite Z.add_0_r; exact Hz)) as (b & Hb & Hv & Hr).
rewrite Hb. f_equal.
rewrite (le_byte_small v 1 0 ltac:(replace (2 ^ (8 * Z.of_nat 1)) with 256 by (vm_compute; reflexivity); lia) ltac:(lia)).
replace (8 * Z.of_nat 0) with 0 by lia.
rewrite Z.shiftr_0_r, Hv, Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma pl_dg0 : bv_unsigned (dg 0) = 48.
Proof. unfold dg. rewrite Z_to_bv_unsigned. reflexivity. Qed.

Lemma pl_map_repeat48 : forall r, map bv_unsigned (repeat (dg 0) r) = repeat 48 r.
Proof. intros r. induction r as [|r IH]; cbn [repeat map]; [reflexivity | rewrite IH, pl_dg0; reflexivity]. Qed.

Lemma pl_nth_rep : forall r j, (j < r)%nat -> nth j (repeat 48 r) 0 = 48.
Proof.
induction r as [|r IH]; intros j Hj; [lia|].
destruct j as [|j]; cbn [repeat nth]; [reflexivity | apply IH; lia].
Qed.

Lemma pl_garr8_rep : forall (H : word -> bool) (mem : word -> option byte) (base : Z) (r : nat),
(forall i, 0 <= i < Z.of_nat r -> aview SEGS H mem (base + i) = Some 48) ->
garr8 SEGS (mrestrict H mem) base (repeat 48 r).
Proof.
intros H mem base r Hall j Hj. rewrite repeat_length in Hj.
rewrite (pl_nth_rep r j Hj). split; [|lia]. apply pl_val_mem1. apply Hall. lia.
Qed.

(* The ten-byte picture of d after the pad: pre, then the zeros the loop wrote, then the untouched tail. *)
Lemma pl_garr8_out : forall (W : world SEGS) (m m' : word -> option byte) (D nd e : Z) (pre post : list byte),
garr8 SEGS (mrestrict (w_H W) m) D (map bv_unsigned (pre ++ post)) ->
Z.of_nat (length pre) = nd -> (length pre + length post = 10)%nat ->
0 <= nd -> nd <= e -> e <= 10 -> 0 <= D -> D + 10 < 2 ^ 64 ->
(forall i, nd <= i < e -> aview SEGS (w_H W) m' (D + i) = Some 48) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (D + nd <= a < D + e) -> aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a) ->
garr8 SEGS (mrestrict (w_H W) m') D
(map bv_unsigned (pre ++ repeat (dg 0) (Z.to_nat (e - nd)) ++ skipn (Z.to_nat (e - nd)) post)).
Proof.
intros W m m' D nd e pre post GB Hlen Hlen10 H0 Hne He HD0 HD10 HPAD HKEEP.
set (r := Z.to_nat (e - nd)) in *.
assert (Hr : Z.of_nat r = e - nd) by (unfold r; lia).
assert (Hrp : (r <= length post)%nat) by lia.
rewrite map_app in GB. apply (proj1 (garr8_app _ _ _ _ _)) in GB. destruct GB as [GB1 GB2].
rewrite length_map, Hlen in GB2.
rewrite <- (firstn_skipn r post) in GB2. rewrite map_app in GB2.
apply (proj1 (garr8_app _ _ _ _ _)) in GB2. destruct GB2 as [_ GB3].
rewrite length_map, length_firstn in GB3.
replace (Init.Nat.min r (length post)) with r in GB3 by lia.
rewrite !map_app. apply (proj2 (garr8_app _ _ _ _ _)). split.
- apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact GB1|].
  intros a Ha. rewrite length_map in Ha. apply (mbyte_of_aview SEGS). apply HKEEP; lia.
- rewrite length_map, Hlen. apply (proj2 (garr8_app _ _ _ _ _)). split.
  + rewrite pl_map_repeat48. apply pl_garr8_rep.
    intros i Hi. replace (D + nd + i) with (D + (nd + i)) by lia. apply HPAD. lia.
  + rewrite pl_map_repeat48, repeat_length.
    apply (garr8_frame SEGS (mrestrict (w_H W) m)); [exact GB3|].
    intros a Ha. rewrite length_map, length_skipn in Ha.
    apply (mbyte_of_aview SEGS). apply HKEEP; lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The loop at 0x82a38 (offset 0x22c4), by induction on the pad count.  *)
(* ------------------------------------------------------------------ *)

Lemma pl_loop : forall (n : nat) (j mn nd : Z) W (regs : bvmap 5 word) memc mdc
STK sp0 FP ly S W0 mem0 md0 own lyc Sc pos k,
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc Sc W memc mdc k ->
Z.of_nat n = mn - j -> 0 <= nd -> nd <= j -> j < mn -> mn <= 10 ->
getr regs 5 = w64 (frame_addr lyc 0 pos + 32 + j) ->
getr regs 6 = w64 48 ->
getr regs 11 = w64 (frame_addr lyc 0 pos + 32 + j) ->
getr regs 16 = w64 nd ->
getr regs 17 = w64 (mn - j) ->
getr regs 20 = w64 mn ->
getr regs 22 = w64 SB ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (frame_addr lyc 0 pos + 32) 10 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x22c4)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x2304)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc Sc W mem' md' k /\
(forall r, In r PL_KEPT -> getr regs' r = getr regs r) /\
getr regs' 5 = w64 (frame_addr lyc 0 pos + 32 + mn) /\
getr regs' 11 = w64 (frame_addr lyc 0 pos + 32 + mn) /\
getr regs' 16 = w64 mn /\
(forall i, j <= i < mn -> aview SEGS (w_H W) mem' (frame_addr lyc 0 pos + 32 + i) = Some 48) /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 0 pos + 32 + j <= a < frame_addr lyc 0 pos + 32 + mn) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a)).
Proof.
induction n as [|n IH]; intros j mn nd W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc pos k
HJ Hn H0 Hnj Hjm Hmn H5 H6 H11 H16 H17 H20 H22 HRA; [lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 0 pos HAR Hin) as (HF0 & HFc & HFapp).
destruct (al_frames _ _ LAWS lyc Sc W memc mdc 0 pos HAR Hin) as (HFal & _ & HFpres & _).
change (fs_frame_bytes 0) with 64 in HFc, HFapp, HFpres.
set (F := frame_addr lyc 0 pos) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HFlo : 4096 <= F) by lia.
assert (HFhi : F + 64 <= 140737479966720) by lia.
(* the shadow byte of any d-address is never the byte the loop stores *)
assert (HSHA : forall a x, F + 32 <= a < F + 42 -> F + 32 <= x < F + 42 ->
shadow_of_addr SHADOW_OFF x <> a).
{ intros a x Ha Hx. unfold shadow_of_addr, SHADOW_OFF.
  assert (Hq1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hq2 : x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia. }
assert (HSHB : forall x, F + 32 <= x < F + 42 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64).
{ intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
  assert (Hq1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hq2 : x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia. }
remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r)
by (intros nn r Hnn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E5 : ew E 5 = Z_to_bv 64 (F + 32 + j)) by (rewrite (EE 5%nat 5%bv eq_refl); exact H5).
assert (E6 : ew E 6 = Z_to_bv 64 48) by (rewrite (EE 6%nat 6%bv eq_refl); exact H6).
assert (E11 : ew E 11 = Z_to_bv 64 (F + 32 + j)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E16 : ew E 16 = Z_to_bv 64 nd) by (rewrite (EE 16%nat 16%bv eq_refl); exact H16).
assert (E17 : ew E 17 = Z_to_bv 64 (mn - j)) by (rewrite (EE 17%nat 17%bv eq_refl); exact H17).
assert (E20 : ew E 20 = Z_to_bv 64 mn) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (E5u : bv_unsigned (ew E 5) = F + 32 + j) by (rewrite E5; apply unsigned_lit_small; lia).
assert (HBx : U E PL_Bx = SHADOW_OFF)
by (unfold PL_Bx; rewrite (U_atom E 22 SB E22) by (unfold SB; lia); reflexivity).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (HS : st_ok_pi SEGS VAL E ss_pl_loop
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x22c4)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pl_loop. apply pa_entry_st_ok_full.
  - apply (regs_ok_pin E sr_atoms regs 6%bv (SLit 48)); [exact ER | discriminate |].
    cbn [sv_denot]. exact H6.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold region_ok, pl_store_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite E5u. split; [lia|]. split; [lia|]. split; [|constructor].
    intros o Ho. apply (apresent_writable SEGS). apply (proj1 (HFpres (F + 32 + j + o) ltac:(lia))).
  - cbn [pairwise_disjoint all_disjoint]. repeat split.
  - split; [|split; [exact I | exact I]].
    cbn [f_atoms atoms_ok]. unfold afact_ok, PTR. cbn [af_lo af_hi af_al2].
    rewrite E5, E11, E22, !unsigned_lit_small by (try unfold SB; lia).
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try (unfold SB); lia. }
assert (SHOK : sh_ok SEGS PL_Bx PL_SH E (mrestrict (w_H W) memc)).
{ unfold PL_SH. constructor; [|constructor].
  eapply (shent_app_of_frame SEGS B LAWS lyc Sc W memc mdc E PL_Bx 5%nat (F + 32 + j) 0 pos 0 1);
  [exact HAR | exact Hin | exact HBx | exact (U_atom E 5 (F + 32 + j) E5 ltac:(lia)) | lia | lia |].
  change (fs_frame_bytes 0) with 64. lia. }
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite (U_atom E 11 (F + 32 + j) E11) by lia.
  eapply (obl_of_range SEGS (w_H W) memc E PL_Bx (F + 32 + j) 1 (F + 32) 10);
  [exact HRA | exact HBx | lia | lia]. }
{ eapply (awr_ok_cons_gen E _ _ _ _ _ _ _ _ _ 5%nat (F + 32 + j));
  [reflexivity | exact E5u | | apply awr_ok_nil].
  unfold pl_store_region. cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
  right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
  unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. lia. }
(* the byte 48 is now at d[j] *)
assert (V48 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (F + 32 + j + 0) (N.to_nat 1) 48).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  pose proof (@field_of_region_any SEGS Ex _ 5%nat (F + 32 + j) _ 0 1 0 1 0 1%N (SLit 48)
  (st_ok_pi_region_nth Ex _ _ 0%nat _ HS eq_refl)
  ltac:(cbn [ew ewset extK Nat.eqb]; exact E5u) ltac:(left; reflexivity) ltac:(cbn; lia)) as V end.
  cbn [sv_denot] in V. rewrite unsigned_lit_small in V by lia. exact V. }
assert (A48 : aview SEGS (w_H W) (ms_mem ms) (F + 32 + j) = Some 48).
{ apply (aview_of_val_mem1 SEGS); [|lia]. rewrite Z.add_0_r in V48. exact V48. }
pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => F + 32 + j <= a < F + 32 + j + 1) HFr
ltac:(intros bb wlo whi aa Hinw Hrr; vm_compute in Hinw;
repeat (destruct Hinw as [Hq0 | Hinw]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr;
rewrite ?E5u in Hrr; lia|]); destruct Hinw)) as KEEP1. cbv beta in KEEP1.
assert (HRA1 : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (F + 32) 10).
{ eapply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact HRA].
  intros x Hx. apply KEEP1; [apply HSHB; lia|].
  intros Hcc. apply (HSHA (F + 32 + j) x ltac:(lia) ltac:(lia)). lia. }
clear HF HFr HG.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* a7 - 1 <> 0: one more pad *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
  assert (F17 : ew Ex 17 = Z_to_bv 64 (mn - j)) by (cbn [ew ewset extK Nat.eqb]; exact E17);
  rewrite branch_ne_U, (U_atom_off Ex 17 (mn - j) (-1) F17) in Hc by lia end.
  rewrite U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
  assert (Hlt : j + 1 < mn) by (destruct (Z.eqb_spec (mn - j + -1) 0); [discriminate Hc | lia]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x22c4.
  { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 5%nat (F + 32 + j));
    [reflexivity | cbn [ew ewset extK Nat.eqb]; exact E5u | | apply awr_ok_nil].
    unfold pl_store_region. cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. lia. }
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => F + 32 + j <= a < F + 32 + j + 1) HFr
  ltac:(intros bb wlo whi aa Hinw Hrr; vm_compute in Hinw;
  repeat (destruct Hinw as [Hq0 | Hinw]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr;
  cbn [ew ewset extK Nat.eqb] in Hrr; rewrite ?E5u in Hrr; lia|]); destruct Hinw)) as KEEP2. cbv beta in KEEP2.
  clear HF HFr HG.
  assert (A48b : aview SEGS (w_H W) (ms_mem ms0) (F + 32 + j) = Some 48).
  { lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    pose proof (@field_of_region_any SEGS Ex _ 5%nat (F + 32 + j) _ 0 1 0 1 0 1%N (SLit 48)
    (st_ok_pi_region_nth Ex _ _ 0%nat _ HS eq_refl)
    ltac:(cbn [ew ewset extK Nat.eqb]; exact E5u) ltac:(left; reflexivity) ltac:(cbn; lia)) as V end.
    cbn [sv_denot] in V. rewrite unsigned_lit_small in V by lia. rewrite Z.add_0_r in V.
    apply (aview_of_val_mem1 SEGS); [exact V | lia]. }
  assert (HRA2 : range_addressable (aview SEGS (w_H W) (ms_mem ms0)) SHADOW_OFF (F + 32) 10).
  { eapply (range_addressable_agree (aview SEGS (w_H W) (ms_mem ms))); [|exact HRA1].
    intros x Hx. apply KEEP2; [apply HSHB; lia|].
    intros Hcc. apply (HSHA (F + 32 + j) x ltac:(lia) ltac:(lia)). lia. }
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ PL_KEPT HS
  ltac:(split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE nn Hnn)
  | cbn [ed ewset extK Eimg]; exact (proj2 HAE)]) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pl_rreg HS (5%bv : bv 5) N5. pl_rreg HS (6%bv : bv 5) N6. pl_rreg HS (11%bv : bv 5) N11.
  pl_rreg HS (16%bv : bv 5) N16. pl_rreg HS (17%bv : bv 5) N17. pl_rreg HS (20%bv : bv 5) N20.
  pl_rreg HS (22%bv : bv 5) N22.
  lazymatch type of N5 with _ = sv_denot ?Ex _ =>
  rewrite (pl_denot_off Ex 5 (F + 32 + j) 1 ltac:(cbn [ew ewset extK Nat.eqb]; exact E5) ltac:(lia) ltac:(lia)) in N5;
  rewrite (pl_denot_off Ex 11 (F + 32 + j) 1 ltac:(cbn [ew ewset extK Nat.eqb]; exact E11) ltac:(lia) ltac:(lia)) in N11;
  rewrite (pl_denot_off Ex 17 (mn - j) (-1) ltac:(cbn [ew ewset extK Nat.eqb]; exact E17) ltac:(lia) ltac:(lia)) in N17;
  rewrite (pl_denot_off Ex 16 nd 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E16) ltac:(lia) ltac:(lia)) in N16;
  rewrite (pl_denot_off Ex 20 mn 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E20) ltac:(lia) ltac:(lia)) in N20;
  rewrite (pl_denot_off Ex 22 SB 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E22) ltac:(unfold SB; lia) ltac:(unfold SB; lia)) in N22
  end.
  cbn [sv_denot] in N6.
  pmkst HS.
  eapply SRr_mono.
  { eapply (IH (j + 1) mn nd W _ _ _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc pos k);
    [ exact HJ | lia | lia | lia | lia | lia
    | cbn [ms_regs]; rewrite N5; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N6; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N11; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N16; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N17; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N20; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N22; unfold w64; f_equal; lia
    | cbn [ms_mem]; exact HRA2 ]. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & R5 & R11 & R16 & RPAD & ROUT).
  cbn [ms_regs ms_mem] in HK3, R5, R11, R16, RPAD, ROUT.
  split; [reflexivity|]. exists regs3, mem3, md3.
  split; [reflexivity|]. split; [exact HJ3|].
  split.
  { intros r Hr. rewrite (HK3 r Hr). exact (HK r Hr). }
  split; [exact R5|]. split; [exact R11|]. split; [exact R16|].
  split.
  { intros i Hi. destruct (Z.eq_dec i j) as [-> | Hne].
    - rewrite (ROUT (F + 32 + j) ltac:(lia) ltac:(lia)). exact A48b.
    - apply RPAD. lia. }
  { intros a Ha Hout. rewrite (ROUT a Ha ltac:(lia)).
    rewrite (KEEP2 a Ha ltac:(lia)). apply KEEP1; [exact Ha | lia]. }
- (* a7 - 1 = 0: this was the last pad; fall through to the max *)
  lazymatch type of Hc with branch_taken _ (sv_denot ?Ex _) _ = _ =>
  assert (F17 : ew Ex 17 = Z_to_bv 64 (mn - j)) by (cbn [ew ewset extK Nat.eqb]; exact E17);
  rewrite branch_ne_U, (U_atom_off Ex 17 (mn - j) (-1) F17) in Hc by lia end.
  rewrite U_SLit, (zcanon_id 0) in Hc by (unfold M64; lia).
  assert (Heq : j + 1 = mn) by (destruct (Z.eqb_spec (mn - j + -1) 0); [lia | discriminate Hc]).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 5%nat (F + 32 + j));
    [reflexivity | cbn [ew ewset extK Nat.eqb]; exact E5u | | apply awr_ok_nil].
    unfold pl_store_region. cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
    right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
    unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. lia. }
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => F + 32 + j <= a < F + 32 + j + 1) HFr
  ltac:(intros bb wlo whi aa Hinw Hrr; vm_compute in Hinw;
  repeat (destruct Hinw as [Hq0 | Hinw]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr;
  cbn [ew ewset extK Nat.eqb] in Hrr; rewrite ?E5u in Hrr; lia|]); destruct Hinw)) as KEEP2. cbv beta in KEEP2.
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* mn < nd is impossible: nd <= j < mn *)
    exfalso.
    lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (G20 : ew Ex 20 = Z_to_bv 64 mn) by (cbn [ew ewset extK Nat.eqb]; exact E20);
    assert (G16 : ew Ex 16 = Z_to_bv 64 nd) by (cbn [ew ewset extK Nat.eqb]; exact E16);
    rewrite branch_ltu_U, (U_atom Ex 20 mn G20), (U_atom Ex 16 nd G16) in Hc0 by lia end.
    destruct (Z.ltb_spec mn nd); [lia | discriminate Hc0].
  + paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x2304.
    { eapply (awr_ok_cons_gen _ _ _ _ _ _ _ _ _ _ 5%nat (F + 32 + j));
      [reflexivity | cbn [ew ewset extK Nat.eqb]; exact E5u | | apply awr_ok_nil].
      unfold pl_store_region. cbn [YP09.r_wlo YP09.r_whi]. intros a Ha.
      right. right. right. exists 0, pos. split; [left; reflexivity|]. left.
      unfold in_zr. cbn [fst snd]. change (fs_frame_bytes 0) with 64. lia. }
    pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => F + 32 + j <= a < F + 32 + j + 1) HFr
    ltac:(intros bb wlo whi aa Hinw Hrr; vm_compute in Hinw;
    repeat (destruct Hinw as [Hq0 | Hinw]; [injection Hq0 as <- <- <-; cbn [base_val] in Hrr;
    cbn [ew ewset extK Nat.eqb] in Hrr; rewrite ?E5u in Hrr; lia|]); destruct Hinw)) as KEEP3. cbv beta in KEEP3.
    clear HF HFr HG.
    assert (A48c : aview SEGS (w_H W) (ms_mem ms1) (F + 32 + j) = Some 48).
    { lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      pose proof (@field_of_region_any SEGS Ex _ 5%nat (F + 32 + j) _ 0 1 0 1 0 1%N (SLit 48)
      (st_ok_pi_region_nth Ex _ _ 0%nat _ HS eq_refl)
      ltac:(cbn [ew ewset extK Nat.eqb]; exact E5u) ltac:(left; reflexivity) ltac:(cbn; lia)) as V end.
      cbn [sv_denot] in V. rewrite unsigned_lit_small in V by lia. rewrite Z.add_0_r in V.
      apply (aview_of_val_mem1 SEGS); [exact V | lia]. }
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ PL_KEPT HS
    ltac:(split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE nn Hnn)
    | cbn [ed ewset extK Eimg]; exact (proj2 HAE)]) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pl_rreg HS (5%bv : bv 5) N5. pl_rreg HS (11%bv : bv 5) N11. pl_rreg HS (16%bv : bv 5) N16.
    lazymatch type of N5 with _ = sv_denot ?Ex _ =>
    rewrite (pl_denot_off Ex 5 (F + 32 + j) 1 ltac:(cbn [ew ewset extK Nat.eqb]; exact E5) ltac:(lia) ltac:(lia)) in N5;
    rewrite (pl_denot_off Ex 11 (F + 32 + j) 1 ltac:(cbn [ew ewset extK Nat.eqb]; exact E11) ltac:(lia) ltac:(lia)) in N11;
    rewrite (pl_denot_off Ex 20 mn 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E20) ltac:(lia) ltac:(lia)) in N16
    end.
    pmkst HS.
    apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
    exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|].
    split; [exact HK|].
    split; [cbn [ms_regs]; rewrite N5; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs]; rewrite N11; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs]; rewrite N16; unfold w64; f_equal; lia|].
    split.
    { intros i Hi. assert (i = j) by lia. subst i. cbn [ms_mem]. exact A48c. }
    { intros a Ha Hout. cbn [ms_mem].
      rewrite (KEEP3 a Ha ltac:(lia)), (KEEP2 a Ha ltac:(lia)). apply KEEP1; [exact Ha | lia]. }
Qed.

(* ------------------------------------------------------------------ *)
(* The whole segment, 0x82a24 (offset 0x22b0) .. 0x82a78 (offset 0x2304). *)
(* ------------------------------------------------------------------ *)

Lemma pb_pd_pad : forall W (regs : bvmap 5 word) memc mdc
STK sp0 FP ly S W0 mem0 md0 own lyc Sc pos k (nd mn : Z) (pre post : list byte),
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc Sc W memc mdc k ->
1 <= nd <= 10 -> 0 <= mn <= 10 ->
Z.of_nat (length pre) = nd -> (length pre + length post = 10)%nat ->
getr regs 5 = w64 (frame_addr lyc 0 pos + 32 + nd) ->
getr regs 11 = w64 (frame_addr lyc 0 pos + 32 + nd) ->
getr regs 16 = w64 nd ->
getr regs 17 = w64 nd ->
getr regs 20 = w64 mn ->
getr regs 22 = w64 SB ->
garr8 SEGS (mrestrict (w_H W) memc) (frame_addr lyc 0 pos + 32) (map bv_unsigned (pre ++ post)) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF (frame_addr lyc 0 pos + 32) 10 ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x22b0)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x2304)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc Sc W mem' md' k /\
(forall r, In r PL_KEPT -> getr regs' r = getr regs r) /\
getr regs' 16 = w64 (Z.max nd mn) /\
getr regs' 5 = w64 (frame_addr lyc 0 pos + 32 + Z.max nd mn) /\
getr regs' 11 = w64 (frame_addr lyc 0 pos + 32 + Z.max nd mn) /\
garr8 SEGS (mrestrict (w_H W) mem') (frame_addr lyc 0 pos + 32)
(map bv_unsigned (pre ++ repeat (dg 0) (Z.to_nat (mn - nd)) ++ skipn (Z.to_nat (mn - nd)) post)) /\
range_addressable (aview SEGS (w_H W) mem') SHADOW_OFF (frame_addr lyc 0 pos + 32) 10 /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (frame_addr lyc 0 pos + 32 <= a < frame_addr lyc 0 pos + 42) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a)).
Proof.
intros W regs memc mdc STK sp0 FP ly S W0 mem0 md0 own lyc Sc pos k nd mn pre post
HJ Hnd Hmn Hlen Hlen10 H5 H11 H16 H17 H20 H22 GB HRA.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HAR.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; cbn [app In]; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 0 pos HAR Hin) as (HF0 & HFc & HFapp).
change (fs_frame_bytes 0) with 64 in HFc, HFapp.
set (F := frame_addr lyc 0 pos) in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
assert (HFlo : 4096 <= F) by lia.
assert (HFhi : F + 64 <= 140737479966720) by lia.
assert (HSHB : forall x, F + 32 <= x < F + 42 -> 0 <= shadow_of_addr SHADOW_OFF x < 2 ^ 64).
{ intros x Hx. unfold shadow_of_addr, SHADOW_OFF.
  assert (Hq1 : 0 <= x / 8) by (apply Z.div_pos; lia).
  assert (Hq2 : x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia. }
remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs r)
by (intros nn r Hnn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hnn).
assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
by (rewrite HE; split; [intros nn Hnn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (E5 : ew E 5 = Z_to_bv 64 (F + 32 + nd)) by (rewrite (EE 5%nat 5%bv eq_refl); exact H5).
assert (E11 : ew E 11 = Z_to_bv 64 (F + 32 + nd)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E16 : ew E 16 = Z_to_bv 64 nd) by (rewrite (EE 16%nat 16%bv eq_refl); exact H16).
assert (E17 : ew E 17 = Z_to_bv 64 nd) by (rewrite (EE 17%nat 17%bv eq_refl); exact H17).
assert (E20 : ew E 20 = Z_to_bv 64 mn) by (rewrite (EE 20%nat 20%bv eq_refl); exact H20).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact H22).
assert (ER : regs_ok E sr_atoms regs) by (rewrite HE; apply regs_ok_Eimg_Ereg).
clear HE.
assert (HS : st_ok_pi SEGS VAL E ss_pl_entry
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x22b0)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold ss_pl_entry. apply pa_entry_st_ok_full.
  - exact ER.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - split; [exact I | split; [exact I | exact I]]. }
assert (SHOK : sh_ok SEGS PL_Bx (@nil shent) E (mrestrict (w_H W) memc)) by apply Forall_nil.
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* nd >= mn: no padding *)
  rewrite branch_geu_U, (U_atom E 17 nd E17), (U_atom E 20 mn E20) in Hc by lia.
  assert (Hskip : mn <= nd) by (destruct (Z.ltb_spec nd mn); [discriminate Hc | lia]).
  paj_run_tok RUN HS HJ SHOK Bspan.
  { apply awr_ok_nil. }
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => False) HFr
  ltac:(intros bb wlo whi aa Hinw Hrr; vm_compute in Hinw; destruct Hinw)) as KEEP1. cbv beta in KEEP1.
  clear HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK Bspan.
  + (* mn < nd: a6 keeps nd *)
    lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (G20 : ew Ex 20 = Z_to_bv 64 mn) by (cbn [ew ewset extK Nat.eqb]; exact E20);
    assert (G16 : ew Ex 16 = Z_to_bv 64 nd) by (cbn [ew ewset extK Nat.eqb]; exact E16);
    rewrite branch_ltu_U, (U_atom Ex 20 mn G20), (U_atom Ex 16 nd G16) in Hc0 by lia end.
    assert (Hlt : mn < nd) by (destruct (Z.ltb_spec mn nd); [lia | discriminate Hc0]).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x2304.
    { apply awr_ok_nil. }
    pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => False) HFr
    ltac:(intros bb wlo whi aa Hinw Hrr; vm_compute in Hinw; destruct Hinw)) as KEEP2. cbv beta in KEEP2.
    clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ PL_KEPT HS
    ltac:(split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE nn Hnn)
    | cbn [ed ewset extK Eimg]; exact (proj2 HAE)]) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pl_rreg HS (5%bv : bv 5) N5. pl_rreg HS (11%bv : bv 5) N11. pl_rreg HS (16%bv : bv 5) N16.
    lazymatch type of N5 with _ = sv_denot ?Ex _ =>
    rewrite (pl_denot_off Ex 5 (F + 32 + nd) 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E5) ltac:(lia) ltac:(lia)) in N5;
    rewrite (pl_denot_off Ex 11 (F + 32 + nd) 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E11) ltac:(lia) ltac:(lia)) in N11;
    rewrite (pl_denot_off Ex 16 nd 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E16) ltac:(lia) ltac:(lia)) in N16
    end.
    pmkst HS.
    assert (KEEPa : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
    by (intros a Ha; rewrite (KEEP2 a Ha ltac:(tauto)); apply KEEP1; [exact Ha | tauto]).
    apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
    exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|]. split; [exact HK|].
    split; [cbn [ms_regs]; rewrite N16; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs]; rewrite N5; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs]; rewrite N11; unfold w64; f_equal; lia|].
    split.
    { replace (Z.to_nat (mn - nd)) with (Z.to_nat (nd - nd)) by lia. cbn [ms_mem].
      eapply (pl_garr8_out W memc _ (F + 32) nd nd pre post GB Hlen Hlen10);
      [lia | lia | lia | lia | lia | intros i Hi; lia | intros a Ha _; apply KEEPa; lia]. }
    split.
    { cbn [ms_mem]. eapply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact HRA].
      intros x Hx. apply KEEPa. apply HSHB. lia. }
    { intros a Ha _. cbn [ms_mem]. apply KEEPa. exact Ha. }
  + (* nd <= mn, with mn <= nd: a6 := mn = nd *)
    lazymatch type of Hc0 with branch_taken _ (sv_denot ?Ex _) _ = _ =>
    assert (G20 : ew Ex 20 = Z_to_bv 64 mn) by (cbn [ew ewset extK Nat.eqb]; exact E20);
    assert (G16 : ew Ex 16 = Z_to_bv 64 nd) by (cbn [ew ewset extK Nat.eqb]; exact E16);
    rewrite branch_ltu_U, (U_atom Ex 20 mn G20), (U_atom Ex 16 nd G16) in Hc0 by lia end.
    assert (Heq : mn = nd) by (destruct (Z.ltb_spec mn nd); [discriminate Hc0 | lia]).
    paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x2304.
    { apply awr_ok_nil. }
    pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => False) HFr
    ltac:(intros bb wlo whi aa Hinw Hrr; vm_compute in Hinw; destruct Hinw)) as KEEP2. cbv beta in KEEP2.
    clear HF HFr HG.
    pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ PL_KEPT HS
    ltac:(split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE nn Hnn)
    | cbn [ed ewset extK Eimg]; exact (proj2 HAE)]) ltac:(vm_compute; reflexivity)) as HK.
    cbn [ms_regs restrict] in HK.
    pl_rreg HS (5%bv : bv 5) N5. pl_rreg HS (11%bv : bv 5) N11. pl_rreg HS (16%bv : bv 5) N16.
    lazymatch type of N5 with _ = sv_denot ?Ex _ =>
    rewrite (pl_denot_off Ex 5 (F + 32 + nd) 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E5) ltac:(lia) ltac:(lia)) in N5;
    rewrite (pl_denot_off Ex 11 (F + 32 + nd) 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E11) ltac:(lia) ltac:(lia)) in N11;
    rewrite (pl_denot_off Ex 20 mn 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E20) ltac:(lia) ltac:(lia)) in N16
    end.
    pmkst HS.
    assert (KEEPa : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
    by (intros a Ha; rewrite (KEEP2 a Ha ltac:(tauto)); apply KEEP1; [exact Ha | tauto]).
    apply SRr_ret. split; [reflexivity|].
    lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
    exists (ms_regs msx), (ms_mem msx), mdx end.
    split; [reflexivity|]. split; [exact HJ|]. split; [exact HK|].
    split; [cbn [ms_regs]; rewrite N16; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs]; rewrite N5; unfold w64; f_equal; lia|].
    split; [cbn [ms_regs]; rewrite N11; unfold w64; f_equal; lia|].
    split.
    { replace (Z.to_nat (mn - nd)) with (Z.to_nat (nd - nd)) by lia. cbn [ms_mem].
      eapply (pl_garr8_out W memc _ (F + 32) nd nd pre post GB Hlen Hlen10);
      [lia | lia | lia | lia | lia | intros i Hi; lia | intros a Ha _; apply KEEPa; lia]. }
    split.
    { cbn [ms_mem]. eapply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact HRA].
      intros x Hx. apply KEEPa. apply HSHB. lia. }
    { intros a Ha _. cbn [ms_mem]. apply KEEPa. exact Ha. }
- (* nd < mn: run the pad loop *)
  rewrite branch_geu_U, (U_atom E 17 nd E17), (U_atom E 20 mn E20) in Hc by lia.
  assert (Hpad : nd < mn) by (destruct (Z.ltb_spec nd mn); [lia | discriminate Hc]).
  paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x22c4.
  { apply awr_ok_nil. }
  pose proof (kept_of_frame (segs:=SEGS) _ _ _ _ _ (fun a => False) HFr
  ltac:(intros bb wlo whi aa Hinw Hrr; vm_compute in Hinw; destruct Hinw)) as KEEP1. cbv beta in KEEP1.
  clear HF HFr HG.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ PL_KEPT HS
  ltac:(split; [intros nn Hnn; rewrite ?ew_ewset_other by lia; exact (proj1 HAE nn Hnn)
  | cbn [ed ewset extK Eimg]; exact (proj2 HAE)]) ltac:(vm_compute; reflexivity)) as HK.
  cbn [ms_regs restrict] in HK.
  pl_rreg HS (5%bv : bv 5) N5. pl_rreg HS (6%bv : bv 5) N6. pl_rreg HS (11%bv : bv 5) N11.
  pl_rreg HS (16%bv : bv 5) N16. pl_rreg HS (17%bv : bv 5) N17. pl_rreg HS (20%bv : bv 5) N20.
  pl_rreg HS (22%bv : bv 5) N22.
  lazymatch type of N5 with _ = sv_denot ?Ex _ =>
  rewrite (pl_denot_off Ex 5 (F + 32 + nd) 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E5) ltac:(lia) ltac:(lia)) in N5;
  rewrite (pl_denot_off Ex 11 (F + 32 + nd) 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E11) ltac:(lia) ltac:(lia)) in N11;
  rewrite (pl_denot_off Ex 16 nd 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E16) ltac:(lia) ltac:(lia)) in N16;
  rewrite (pl_denot_off Ex 20 mn 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E20) ltac:(lia) ltac:(lia)) in N20;
  rewrite (pl_denot_off Ex 22 SB 0 ltac:(cbn [ew ewset extK Nat.eqb]; exact E22) ltac:(unfold SB; lia) ltac:(unfold SB; lia)) in N22;
  rewrite (pl_sub32 Ex mn nd ltac:(cbn [ew ewset extK Nat.eqb]; exact E20) ltac:(cbn [ew ewset extK Nat.eqb]; exact E16)
  ltac:(lia) ltac:(lia) ltac:(lia)) in N17
  end.
  cbn [sv_denot] in N6.
  assert (HRA1 : range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (F + 32) 10).
  { eapply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact HRA].
    intros x Hx. apply KEEP1; [apply HSHB; lia | tauto]. }
  pmkst HS.
  eapply SRr_mono.
  { eapply (pl_loop (Z.to_nat (mn - nd)) nd mn nd W _ _ _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc pos k);
    [ exact HJ | lia | lia | lia | lia | lia
    | cbn [ms_regs]; rewrite N5; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N6; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N11; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N16; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N17; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N20; unfold w64; f_equal; lia
    | cbn [ms_regs]; rewrite N22; unfold w64; f_equal; lia
    | cbn [ms_mem]; exact HRA1 ]. }
  cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HK3 & R5 & R11 & R16 & RPAD & ROUT).
  cbn [ms_mem ms_regs] in HK3, R5, R11, R16, RPAD, ROUT.
  assert (KEEPa : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 42) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a)
  by (intros a Ha Hout; rewrite (ROUT a Ha ltac:(lia)); apply KEEP1; [exact Ha | tauto]).
  split; [reflexivity|]. exists regs3, mem3, md3.
  split; [reflexivity|]. split; [exact HJ3|].
  split; [intros r Hr; rewrite (HK3 r Hr); exact (HK r Hr)|].
  split; [rewrite R16; unfold w64; f_equal; lia|].
  split; [rewrite R5; unfold w64; f_equal; lia|].
  split; [rewrite R11; unfold w64; f_equal; lia|].
  split.
  { eapply (pl_garr8_out W memc mem3 (F + 32) nd mn pre post GB Hlen Hlen10);
    [lia | lia | lia | lia | lia | |].
    - intros i Hi. apply RPAD. lia.
    - intros a Ha Hout. rewrite (ROUT a Ha ltac:(lia)). apply KEEP1; [exact Ha | tauto]. }
  split.
  { eapply (range_addressable_agree (aview SEGS (w_H W) memc)); [|exact HRA].
    intros x Hx. apply KEEPa; [apply HSHB; lia | ].
    unfold shadow_of_addr, SHADOW_OFF.
    assert (Hq1 : 0 <= x / 8) by (apply Z.div_pos; lia).
    assert (Hq2 : x / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). lia. }
  { intros a Ha Hout. apply KEEPa; [exact Ha | exact Hout]. }
Qed.

Print Assumptions pb_pd_pad.

(* ---- the copy loop ---- *)
(* The loop at 0x82a90 (offset 0x231c), one lemma by induction on a nat fuel.  `done` is what the loop has
   already copied to b + N, `pre` the digits still at D that it copies in reverse. *)
(* What the copy-out segment needs of a range it reads: visible, out of the runtime's stack below sp,
   addressable, in app memory and in range. The hull of the shadow bytes is not needed: the segment
   reads one shadow byte per access, never a hull. *)
Definition tsrc0_ok (W : world SEGS) (memc : word -> option byte) (sp q n : Z) : Prop :=
(forall a, q <= a < q + n -> aview SEGS (w_H W) memc a <> None /\ ~ (sp - ESTACK <= a < sp)) /\
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF q n /\ amem_range q n /\ 0 <= q /\ q + n <= 2 ^ 63.

Lemma pd_cl_loop : forall (fuel : nat) (pre done : list Z)
(W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model)
(STK sp0 ev : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (pos : Z)
(lyc : alayout) (Sc : astate) (p b N D nd np : Z),
Z.of_nat (length done) = nd -> Z.of_nat (length pre) = np ->
(length pre <= fuel)%nat -> 0 < np -> nd + np <= 10 ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc Sc W memc mdc ev ->
In (0, pos) (frames Sc) -> D = frame_addr lyc 0 pos + 32 ->
0 <= b -> 0 <= N -> p mod 8 = 0 ->
getr regs 5 = w64 10 -> getr regs 6 = w64 (SB + p / 8) -> getr regs 7 = w64 18446744073709551615 ->
getr regs 14 = w64 D -> getr regs 15 = w64 (18446744073709551615 - D) ->
getr regs 16 = w64 (np - 1) -> getr regs 17 = w64 (18446744073709551615 - b) ->
getr regs 18 = w64 p -> getr regs 19 = w64 b -> getr regs 22 = w64 SB ->
twr_ok B STK sp0 FP ly S lyc Sc ((0, pos) :: own) W memc (spZ regs) p 8 ->
twr_ok B STK sp0 FP ly S lyc Sc ((0, pos) :: own) W memc (spZ regs) (b + N) (nd + np) ->
tsrc0_ok W memc (spZ regs) p 8 ->
tsrc0_ok W memc (spZ regs) (b + N) (nd + np) ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF D np ->
(p + 8 <= b + N \/ b + N + (nd + np) <= p) ->
(p + 8 <= D \/ D + np <= p) ->
(b + N + (nd + np) <= D \/ D + np <= b + N) ->
val_mem SEGS (mrestrict (w_H W) memc) p 8 (N + nd) ->
garr8 SEGS (mrestrict (w_H W) memc) (b + N) done ->
garr8 SEGS (mrestrict (w_H W) memc) D pre ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x231c)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x2398)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc Sc W mem' md' ev /\
(forall r, In r PD_CLB_KEPT -> getr regs' r = getr regs r) /\
garr8 SEGS (mrestrict (w_H W) mem') (b + N) (done ++ rev pre) /\
val_mem SEGS (mrestrict (w_H W) mem') p 8 (N + nd + np) /\
garr8 SEGS (mrestrict (w_H W) mem') D pre /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + 8) -> ~ (b + N <= a < b + N + (nd + np)) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
induction fuel as [|fuel IH]; intros pre done W regs memc mdc STK sp0 ev FP ly S W0 mem0 md0 own pos lyc Sc
p b N D nd np Hnd Hnp Hfuel Hnp0 HK10 HJ Hfr HD Hb0 HN0 Hp8 R5 R6 R7 R14 R15 R16 R17 R18 R19 R22
HWP HWB HSP HSB HRD Hdj1 Hdj2 Hdj3 HVP HGB HGD;
[exfalso; destruct pre as [|x pre]; cbn [length] in *; lia|].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCR. unfold YG0f.ASAN_CEIL in HCR.
pose proof (proj1 HJ) as HAR.
(* the digit buffer's bounds, from the frame it lives in *)
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 0 pos HAR Hfr) as (HF4096 & HFceil & HFapp).
assert (HFB : fs_frame_bytes 0 = 64) by reflexivity. rewrite HFB in HFceil.
pose proof HSP as (HSP1 & HSP2 & HSP4 & HSP5 & HSP6).
pose proof HSB as (HSB1 & HSB2 & HSB4 & HSB5 & HSB6).
assert (HPlo : 0 <= p) by lia.
assert (HPhi : p + 8 <= 2 ^ 47 - 1)
by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HSP4; lia).
assert (HPdm : p = 8 * (p / 8)) by (pose proof (Z.div_mod p 8 ltac:(lia)); lia).
assert (HPhi16 : p <= 2 ^ 47 - 16) by lia.
assert (HBhi : b + N + (nd + np) <= 2 ^ 47 - 1)
by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HSB4; lia).
assert (HDlo : 0 <= D) by lia.
assert (HDhi : D + np <= 2 ^ 47 - 2) by lia.
(* split off the last digit: the loop copies it first *)
destruct (exists_last (l := pre) ltac:(intros ->; cbn [length] in Hnp; lia)) as (pre' & c & ->).
set (m := length pre') in *.
assert (Hlen : Z.of_nat m + 1 = np) by (rewrite <- Hnp, length_app; cbn [length]; lia).
destruct (proj1 (garr8_app SEGS (mrestrict (w_H W) memc) D pre' [c]) HGD) as (HGD1 & HGD2).
destruct (HGD2 0%nat ltac:(cbn [length]; lia)) as (HVC & HCB).
cbn [Z.of_nat nth] in HVC, HCB. rewrite Z.add_0_r in HVC.
(* the environment: atoms 32..35 are the counter, the destination byte, the digit's address, the digit *)
remember (Eimg (Ereg regs [Z_to_bv 64 (N + nd); Z_to_bv 64 (b + N + nd);
Z_to_bv 64 (D + Z.of_nat m); Z_to_bv 64 c])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [Z_to_bv 64 (N + nd); Z_to_bv 64 (b + N + nd);
Z_to_bv 64 (D + Z.of_nat m); Z_to_bv 64 c]) E)
by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E5 : ew E 5 = Z_to_bv 64 10) by (rewrite (EE 5%nat 5%bv eq_refl); exact R5).
assert (E6 : ew E 6 = Z_to_bv 64 (SB + p / 8)) by (rewrite (EE 6%nat 6%bv eq_refl); exact R6).
assert (E7 : ew E 7 = Z_to_bv 64 18446744073709551615) by (rewrite (EE 7%nat 7%bv eq_refl); exact R7).
assert (E14 : ew E 14 = Z_to_bv 64 D) by (rewrite (EE 14%nat 14%bv eq_refl); exact R14).
assert (E15 : ew E 15 = Z_to_bv 64 (18446744073709551615 - D)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15).
assert (E16 : ew E 16 = Z_to_bv 64 (Z.of_nat m)) by (rewrite (EE 16%nat 16%bv eq_refl), R16; f_equal; lia).
assert (E17 : ew E 17 = Z_to_bv 64 (18446744073709551615 - b)) by (rewrite (EE 17%nat 17%bv eq_refl); exact R17).
assert (E18 : ew E 18 = Z_to_bv 64 p) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 b) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E32 : ew E 32 = Z_to_bv 64 (N + nd))
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (b + N + nd))
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (D + Z.of_nat m))
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 c)
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (U18 : bv_unsigned (ew E 18) = p) by (rewrite E18; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = b + N + nd) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = D + Z.of_nat m) by (rewrite E34; apply unsigned_lit_small; lia).
assert (HBx : U E cl_Bx = SHADOW_OFF)
by (unfold cl_Bx; rewrite (U_atom E 22 SB E22) by (unfold SB; lia); reflexivity).
(* the symbolic state at the loop head *)
assert (HS : st_ok_pi SEGS VAL E cl_ss
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x231c)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold cl_ss. apply pa_entry_st_ok_full.
- unfold cl_regs. apply regs_ok_pin;
[ apply regs_ok_pin;
  [ apply regs_ok_pin;
    [ rewrite HE; apply regs_ok_Eimg_Ereg
    | intros X; discriminate X
    | cbn [sv_denot]; exact R5 ]
  | intros X; discriminate X
  | rewrite (denot_shx E 18 22 0 p SB E18 E22) by (unfold SB; lia); rewrite Z.add_0_r; exact R6 ]
| intros X; discriminate X
| cbn [sv_denot]; exact R7 ].
- vm_compute. reflexivity.
- unfold cl_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
+ rewrite U18. split; [lia|]. split; [lia|]. split.
* intros o Ho. apply (apresent_writable SEGS). exact (proj1 (proj2 (HWP (p + o) ltac:(lia)))).
* constructor; [|constructor].
apply (chunk_ok_val SEGS E _ p 0 8 (SOff 32 0) (N + nd));
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact HVP.
+ rewrite U34. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (D + Z.of_nat m) 0 1 (SOff 35 0) c);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
rewrite Z.add_0_r. exact HVC.
+ rewrite U33. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS).
exact (proj1 (proj2 (HWB (b + N + nd + o) ltac:(lia)))).
- unfold cl_mem. cbn [pairwise_disjoint all_disjoint].
repeat match goal with |- _ /\ _ => split end;
first [ exact I
| unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
rewrite ?U18, ?U33, ?U34; lia ].
- split; [|split; [exact I|]].
+ unfold cl_facts. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E14, E15, E16, E17, E18, E19, E22, E32, E33, E34, E35.
rewrite !unsigned_lit_small by (try unfold SB; lia).
change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
repeat match goal with |- _ /\ _ => split end;
first [ exact I | exact Hp8 | (try unfold SB); lia ].
+ unfold cl_facts. cbn [f_alias alias_ok]. split; [|split; [|exact I]].
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 14 D E14), (U_atom E 16 (Z.of_nat m) E16), (U_atom E 34 (D + Z.of_nat m) E34) by lia.
rewrite zcanon_id by (unfold M64; lia). lia.
* apply U_inj. rewrite U_SAlu. cbn [zalu_raw].
rewrite (U_atom E 19 b E19), (U_atom E 32 (N + nd) E32), (U_atom E 33 (b + N + nd) E33) by lia.
rewrite zcanon_id by (unfold M64; lia). lia. }
(* the two covered shadow ranges *)
assert (SHOK : sh_ok SEGS cl_Bx cl_SH E (mrestrict (w_H W) memc)).
{ unfold cl_SH. constructor; [|constructor; [|constructor]].
- apply (shent_ok_of_range SEGS (w_H W) memc E cl_Bx 18 p 8 p 0 8 HSP2 HBx
ltac:(exact (U_atom E 18 p E18 ltac:(lia))) ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx.
exact (cl_amem_out_band p 8 x HSP4 ltac:(lia)).
- apply (shent_ok_of_range SEGS (w_H W) memc E cl_Bx 33 (b + N) (nd + np) (b + N + nd) 0 1
HSB2 HBx ltac:(exact (U_atom E 33 (b + N + nd) E33 ltac:(lia))) ltac:(lia) ltac:(lia)).
intros x Hx. cbn [Z.min Z.max] in Hx.
exact (cl_amem_out_band (b + N) (nd + np) x HSB4 ltac:(lia)). }
clear HE.
(* one pass of the loop body, up to the back-edge branch at 0x2374 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ rewrite (U_atom E 34 (D + Z.of_nat m) E34) by lia.
eapply (obl_of_range SEGS (w_H W) memc E cl_Bx _ 1 D np HRD HBx); lia. }
{ cl_awr HWP HWB U18 U33. }
(* after the body: read the new memory out of the symbolic state *)
assert (VNEW : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (b + N + nd + 0) 1 c).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (@field_of_region_any SEGS Ex (mrestrict (w_H W) (ms_mem ms)) 33%nat (b + N + nd)
_ 0 1 0 1 0 1%N (SOff 35 0)
(st_ok_pi_region_nth _ _ _ 2%nat _ HS eq_refl)
ltac:(rewrite ?ew_ewset_other by lia; exact U33) ltac:(left; reflexivity) ltac:(cbn; lia)) as V;
change (bv_unsigned (sv_denot Ex (SOff 35 0))) with (U Ex (SOff 35 0)) in V;
rewrite (U_atom Ex 35 c ltac:(rewrite ?ew_ewset_other by lia; exact E35) ltac:(lia)) in V end.
change (2 ^ (8 * Z.of_N 1)) with 256 in V. rewrite (Z.mod_small c 256) in V by lia.
change (N.to_nat 1) with 1%nat in V. exact V. }
assert (VCNT : val_mem SEGS (mrestrict (w_H W) (ms_mem ms)) (p + 0) 8 (N + nd + 1)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (@field_of_region_any SEGS Ex (mrestrict (w_H W) (ms_mem ms)) 18%nat p
_ 0 8 0 8 0 8%N (SOff 32 1)
(st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl)
ltac:(rewrite ?ew_ewset_other by lia; exact U18) ltac:(left; reflexivity) ltac:(cbn; lia)) as V;
change (bv_unsigned (sv_denot Ex (SOff 32 1))) with (U Ex (SOff 32 1)) in V;
rewrite (U_atom_off Ex 32 (N + nd) 1 ltac:(rewrite ?ew_ewset_other by lia; exact E32)
ltac:(lia) ltac:(lia)) in V end.
change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616 in V.
rewrite (Z.mod_small (N + nd + 1) 18446744073709551616) in V by lia.
change (N.to_nat 8) with 8%nat in V. exact V. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
(fun a => (p <= a < p + 8) \/ (b + N + nd <= a < b + N + nd + 1)) HFr
ltac:(intros bq wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq0 | Hin];
[injection Hq0 as <- <- <-; cbn [base_val] in Hrr; rewrite ?U18, ?U33, ?U34 in Hrr; lia|]);
destruct Hin)) as KEEP1.
assert (GBNEW : garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) (b + N) (done ++ [c])).
{ apply (garr8_app1 SEGS (mrestrict (w_H W) memc)); [exact HGB | | lia |].
- rewrite Hnd. replace (b + N + nd) with (b + N + nd + 0) by lia. exact VNEW.
- intros a Ha. apply (mbyte_of_aview SEGS). apply KEEP1; [lia|]. rewrite Hnd in Ha. lia. }
assert (GDNEW : garr8 SEGS (mrestrict (w_H W) (ms_mem ms)) D (pre' ++ [c])).
{ apply (cl_garr8_kept _ memc); [|exact HGD]. intros x Hx.
rewrite length_app in Hx. cbn [length] in Hx. apply KEEP1; [lia|]. lia. }
pose proof HG as HGa.
clear HF HFr HG.
(* the back-edge branch: taken unless the index has wrapped to -1 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
- (* taken: more digits to copy *)
rewrite branch_ne_U, U_SOff, U_SLit in Hc.
rewrite ?ew_ewset_other in Hc by lia.
rewrite E16, unsigned_lit_small in Hc by lia.
assert (Hm0 : (0 < m)%nat).
{ destruct (Z.eq_dec (Z.of_nat m) 0) as [Hz | Hz]; [exfalso | lia].
rewrite Hz in Hc. vm_compute in Hc. discriminate Hc. }
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x231c. { cl_awr HWP HWB U18 U33. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
(fun a => (p <= a < p + 8) \/ (b + N + nd <= a < b + N + nd + 1)) HFr
ltac:(intros bq wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq0 | Hin];
[injection Hq0 as <- <- <-; cbn [base_val] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?U18, ?U33, ?U34 in Hrr; lia|]);
destruct Hin)) as KEEP2.
assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
~ ((p <= a < p + 8) \/ (b + N + nd <= a < b + N + nd + 1)) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
by (intros a Ha Hn; rewrite (KEEP2 a Ha Hn); exact (KEEP1 a Ha Hn)).
assert (KEEPB2 : forall a, SHADOW_OFF <= a < kHighShadowEnd ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply KEEP; [unfold SHADOW_OFF, kHighShadowEnd in Ha; lia|].
intros [Hx | Hx]; [exact (cl_amem_out_band p 8 a HSP4 ltac:(lia) Ha)
| exact (cl_amem_out_band (b + N) (nd + np) a HSB4 ltac:(lia) Ha)]. }
assert (GROW : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms0) a)
by (intros a Hpr; apply (apresent_grows (w_H W) (ms_mem ms) (ms_mem ms0) a HG);
apply (apresent_grows (w_H W) memc (ms_mem ms) a HGa); exact Hpr).
(* the two bytes the body wrote are inside the write windows, so read them off the state again *)
assert (VNEW2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (b + N + nd) 1 c).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (@field_of_region_any SEGS Ex (mrestrict (w_H W) (ms_mem ms0)) 33%nat (b + N + nd)
_ 0 1 0 1 0 1%N (SOff 35 0)
(st_ok_pi_region_nth _ _ _ 2%nat _ HS eq_refl)
ltac:(rewrite ?ew_ewset_other by lia; exact U33) ltac:(left; reflexivity) ltac:(cbn; lia)) as V;
change (bv_unsigned (sv_denot Ex (SOff 35 0))) with (U Ex (SOff 35 0)) in V;
rewrite (U_atom Ex 35 c ltac:(rewrite ?ew_ewset_other by lia; exact E35) ltac:(lia)) in V end.
change (2 ^ (8 * Z.of_N 1)) with 256 in V. rewrite (Z.mod_small c 256) in V by lia.
change (N.to_nat 1) with 1%nat in V. rewrite Z.add_0_r in V. exact V. }
assert (VCNT2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) p 8 (N + nd + 1)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (@field_of_region_any SEGS Ex (mrestrict (w_H W) (ms_mem ms0)) 18%nat p
_ 0 8 0 8 0 8%N (SOff 32 1)
(st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl)
ltac:(rewrite ?ew_ewset_other by lia; exact U18) ltac:(left; reflexivity) ltac:(cbn; lia)) as V;
change (bv_unsigned (sv_denot Ex (SOff 32 1))) with (U Ex (SOff 32 1)) in V;
rewrite (U_atom_off Ex 32 (N + nd) 1 ltac:(rewrite ?ew_ewset_other by lia; exact E32)
ltac:(lia) ltac:(lia)) in V end.
change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616 in V.
rewrite (Z.mod_small (N + nd + 1) 18446744073709551616) in V by lia.
change (N.to_nat 8) with 8%nat in V. rewrite Z.add_0_r in V. exact V. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ PD_CLB_KEPT HS ltac:(env_agree_chain HAE)
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prregR HS (5%bv : bv 5) N5. prregR HS (6%bv : bv 5) N6. prregR HS (7%bv : bv 5) N7.
prregR HS (16%bv : bv 5) N16.
lazymatch type of N16 with _ = sv_denot ?Ex _ =>
rewrite (cl_denot_of_U Ex _ _ (U_atom_off Ex 16 (Z.of_nat m) (-1)
ltac:(rewrite ?ew_ewset_other by lia; exact E16) ltac:(lia) ltac:(lia))) in N16 end.
lazymatch type of N6 with _ = sv_denot ?Ex _ =>
rewrite (denot_shx Ex 18 22 0 p SB
ltac:(rewrite ?ew_ewset_other by lia; exact E18)
ltac:(rewrite ?ew_ewset_other by lia; exact E22) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(unfold SB; lia)) in N6 end.
rewrite Z.add_0_r in N6. cbn [sv_denot] in N5, N7.
pmkst HS.
eapply SRr_mono.
{ eapply (IH pre' (done ++ [c]) W (ms_regs ms0) (ms_mem ms0) _ STK sp0 ev FP ly S W0 mem0 md0 own pos
lyc Sc p b N D (nd + 1) (np - 1)).
- rewrite length_app. cbn [length]. lia.
- lia.
- lia.
- lia.
- lia.
- exact HJ.
- exact Hfr.
- exact HD.
- exact Hb0.
- exact HN0.
- exact Hp8.
- cbn [ms_regs]. rewrite N5. reflexivity.
- cbn [ms_regs]. rewrite N6. reflexivity.
- cbn [ms_regs]. rewrite N7. reflexivity.
- cbn [ms_regs]. rewrite (HK 14%bv ltac:(cbv; tauto)). exact R14.
- cbn [ms_regs]. rewrite (HK 15%bv ltac:(cbv; tauto)). exact R15.
- cbn [ms_regs]. rewrite N16. unfold w64. f_equal. lia.
- cbn [ms_regs]. rewrite (HK 17%bv ltac:(cbv; tauto)). exact R17.
- cbn [ms_regs]. rewrite (HK 18%bv ltac:(cbv; tauto)). exact R18.
- cbn [ms_regs]. rewrite (HK 19%bv ltac:(cbv; tauto)). exact R19.
- cbn [ms_regs]. rewrite (HK 22%bv ltac:(cbv; tauto)). exact R22.
- unfold spZ. cbn [ms_regs]. rewrite (HK 2%bv ltac:(cbv; tauto)).
intros a Ha. destruct (HWP a Ha) as (HA1 & HA2 & HA3 & HA4).
split; [exact HA1|]. split; [exact (GROW a HA2)|]. split; [exact HA3 | exact HA4].
- unfold spZ. cbn [ms_regs]. rewrite (HK 2%bv ltac:(cbv; tauto)).
intros a Ha. destruct (HWB a ltac:(lia)) as (HA1 & HA2 & HA3 & HA4).
split; [exact HA1|]. split; [exact (GROW a HA2)|]. split; [exact HA3 | exact HA4].
- unfold spZ. cbn [ms_regs]. rewrite (HK 2%bv ltac:(cbv; tauto)).
split; [|split; [|split; [exact HSP4 | split; [exact HSP5 | exact HSP6]]]].
+ intros a Ha. split; [|exact (proj2 (HSP1 a Ha))].
apply (aview_some_of_apresent SEGS). exact (GROW a (proj1 (proj2 (HWP a Ha)))).
+ apply (cl_ra_band _ _ p 8 KEEPB2); [lia | lia | exact HSP2].
- unfold spZ. cbn [ms_regs]. rewrite (HK 2%bv ltac:(cbv; tauto)).
split; [|split; [|split; [|split]]].
+ intros a Ha. split; [|exact (proj2 (HSB1 a ltac:(lia)))].
apply (aview_some_of_apresent SEGS). exact (GROW a (proj1 (proj2 (HWB a ltac:(lia))))).
+ apply (cl_ra_band _ _ (b + N) (nd + 1 + (np - 1)) KEEPB2); [lia | lia|].
apply (range_addressable_sub _ _ (b + N) (nd + np)); [exact HSB2 | lia | lia].
+ unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HSB4 |- *. lia.
+ lia.
+ lia.
- apply (cl_ra_band _ _ D (np - 1) KEEPB2); [lia | lia|].
apply (range_addressable_sub _ _ D np); [exact HRD | lia | lia].
- lia.
- lia.
- lia.
- replace (N + (nd + 1)) with (N + nd + 1) by lia. exact VCNT2.
- apply (garr8_app1 SEGS (mrestrict (w_H W) memc)); [exact HGB | | lia |].
+ rewrite Hnd. exact VNEW2.
+ intros a Ha. apply (mbyte_of_aview SEGS). apply KEEP; [lia|]. rewrite Hnd in Ha. lia.
- apply (cl_garr8_kept _ memc); [|exact HGD1].
intros x Hx. apply KEEP; [lia|]. lia. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ4 & HK3 & GB3 & VP3 & GD3 & KP3 & GR3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ4|].
split.
{ intros r Hr. rewrite (HK3 r Hr). cbn [ms_regs]. exact (HK r Hr). }
split.
{ rewrite <- app_assoc in GB3. cbn [app] in GB3. rewrite rev_unit. exact GB3. }
split.
{ replace (N + nd + np) with (N + (nd + 1) + (np - 1)) by lia. exact VP3. }
split.
{ apply garr8_app. split; [exact GD3|].
apply (cl_garr8_kept _ (ms_mem ms0)).
- intros x Hx. cbn [length Z.of_nat] in Hx. apply KP3; [lia | lia | lia].
- apply (cl_garr8_kept _ (ms_mem ms)).
+ intros x Hx. cbn [length Z.of_nat] in Hx. apply KEEP2; [lia | lia].
+ exact (proj2 (proj1 (garr8_app SEGS _ D pre' [c]) GDNEW)). }
split.
{ intros a Ha Hn1 Hn2. rewrite (KP3 a Ha Hn1 ltac:(lia)). apply KEEP; [exact Ha|]. lia. }
{ intros a Hpr. apply GR3. exact (GROW a Hpr). }
- (* not taken: that was the last digit *)
rewrite branch_ne_U, U_SOff, U_SLit in Hc.
rewrite ?ew_ewset_other in Hc by lia.
rewrite E16, unsigned_lit_small in Hc by lia.
assert (Hm0 : m = 0%nat).
{ destruct (Z.eq_dec (Z.of_nat m) 0) as [Hz | Hz]; [lia | exfalso].
rewrite (zcanon_id (Z.of_nat m + -1)) in Hc by (unfold M64; lia).
rewrite (zcanon_id 18446744073709551615) in Hc by (unfold M64; lia).
destruct (Z.eqb_spec (Z.of_nat m + -1) 18446744073709551615) as [Heq | Hne];
[lia | cbn in Hc; discriminate Hc]. }
assert (Hpre' : pre' = []) by (apply length_zero_iff_nil; exact Hm0).
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x2398. { cl_awr HWP HWB U18 U33. }
pose proof (kept_of_frame (segs := SEGS) _ _ _ _ _
(fun a => (p <= a < p + 8) \/ (b + N + nd <= a < b + N + nd + 1)) HFr
ltac:(intros bq wlo whi a Hin Hrr; vm_compute in Hin;
repeat (destruct Hin as [Hq0 | Hin];
[injection Hq0 as <- <- <-; cbn [base_val] in Hrr;
rewrite ?ew_ewset_other in Hrr by lia; rewrite ?U18, ?U33, ?U34 in Hrr; lia|]);
destruct Hin)) as KEEP2.
(* the two bytes the body wrote are inside the write windows, so read them off the state again *)
assert (VNEW2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) (b + N + nd) 1 c).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (@field_of_region_any SEGS Ex (mrestrict (w_H W) (ms_mem ms0)) 33%nat (b + N + nd)
_ 0 1 0 1 0 1%N (SOff 35 0)
(st_ok_pi_region_nth _ _ _ 2%nat _ HS eq_refl)
ltac:(rewrite ?ew_ewset_other by lia; exact U33) ltac:(left; reflexivity) ltac:(cbn; lia)) as V;
change (bv_unsigned (sv_denot Ex (SOff 35 0))) with (U Ex (SOff 35 0)) in V;
rewrite (U_atom Ex 35 c ltac:(rewrite ?ew_ewset_other by lia; exact E35) ltac:(lia)) in V end.
change (2 ^ (8 * Z.of_N 1)) with 256 in V. rewrite (Z.mod_small c 256) in V by lia.
change (N.to_nat 1) with 1%nat in V. rewrite Z.add_0_r in V. exact V. }
assert (VCNT2 : val_mem SEGS (mrestrict (w_H W) (ms_mem ms0)) p 8 (N + nd + 1)).
{ lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
pose proof (@field_of_region_any SEGS Ex (mrestrict (w_H W) (ms_mem ms0)) 18%nat p
_ 0 8 0 8 0 8%N (SOff 32 1)
(st_ok_pi_region_nth _ _ _ 0%nat _ HS eq_refl)
ltac:(rewrite ?ew_ewset_other by lia; exact U18) ltac:(left; reflexivity) ltac:(cbn; lia)) as V;
change (bv_unsigned (sv_denot Ex (SOff 32 1))) with (U Ex (SOff 32 1)) in V;
rewrite (U_atom_off Ex 32 (N + nd) 1 ltac:(rewrite ?ew_ewset_other by lia; exact E32)
ltac:(lia) ltac:(lia)) in V end.
change (2 ^ (8 * Z.of_N 8)) with 18446744073709551616 in V.
rewrite (Z.mod_small (N + nd + 1) 18446744073709551616) in V by lia.
change (N.to_nat 8) with 8%nat in V. rewrite Z.add_0_r in V. exact V. }
assert (KEEPm : forall a, 0 <= a < 2 ^ 64 ->
~ ((p <= a < p + 8) \/ (b + N + nd <= a < b + N + nd + 1)) ->
aview SEGS (w_H W) (ms_mem ms0) a = aview SEGS (w_H W) memc a)
by (intros a Ha Hn; rewrite (KEEP2 a Ha Hn); exact (KEEP1 a Ha Hn)).
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ PD_CLB_KEPT HS ltac:(env_agree_chain HAE)
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
pmkst HS.
apply SRr_ret. split; [reflexivity|].
lazymatch goal with |- context [mkCfg (mkst (ms_regs ?msx) _ _ _) ?mdx] =>
exists (ms_regs msx), (ms_mem msx), mdx end.
split; [reflexivity|]. split; [exact HJ|]. split; [exact HK|].
split.
{ cbn [ms_mem]. rewrite Hpre'. cbn [app rev].
apply (garr8_app1 SEGS (mrestrict (w_H W) memc)); [exact HGB | | lia |].
- rewrite Hnd. exact VNEW2.
- intros a Ha. apply (mbyte_of_aview SEGS). apply KEEPm; [lia|]. rewrite Hnd in Ha. lia. }
split.
{ cbn [ms_mem]. replace (N + nd + np) with (N + nd + 1) by lia. exact VCNT2. }
split.
{ cbn [ms_mem]. apply (cl_garr8_kept _ (ms_mem ms)); [|exact GDNEW].
intros x Hx. rewrite length_app in Hx. cbn [length] in Hx. apply KEEP2; [lia|].
intros [Hq | Hq]; lia. }
split.
{ cbn [ms_mem]. intros a Ha Hn1 Hn2. apply KEEPm; [exact Ha|]. intros [Hq | Hq]; lia. }
{ cbn [ms_mem]. intros a Hpr. apply (apresent_grows (w_H W) (ms_mem ms) _ a HG).
apply (apresent_grows (w_H W) memc (ms_mem ms) a HGa). exact Hpr. }
Qed.

(* The whole segment 0x2304 .. 0x2398 (0x82a78 .. 0x82b0c): the six setup instructions and the loop. *)
Lemma pd_copy_seg : forall (pre : list Z)
(W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte) (mdc : Model)
(STK sp0 ev : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world SEGS)
(mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (pos : Z)
(lyc : alayout) (Sc : astate) (p b N D K : Z),
Z.of_nat (length pre) = K -> 1 <= K <= 10 ->
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc Sc W memc mdc ev ->
In (0, pos) (frames Sc) -> D = frame_addr lyc 0 pos + 32 ->
0 <= b -> 0 <= N -> p mod 8 = 0 ->
getr regs 14 = w64 D -> getr regs 15 = w64 (Z.lxor D 18446744073709551615) ->
getr regs 16 = w64 K ->
getr regs 18 = w64 p -> getr regs 19 = w64 b -> getr regs 22 = w64 SB ->
twr_ok B STK sp0 FP ly S lyc Sc ((0, pos) :: own) W memc (spZ regs) p 8 ->
twr_ok B STK sp0 FP ly S lyc Sc ((0, pos) :: own) W memc (spZ regs) (b + N) K ->
tsrc0_ok W memc (spZ regs) p 8 ->
tsrc0_ok W memc (spZ regs) (b + N) K ->
range_addressable (aview SEGS (w_H W) memc) SHADOW_OFF D K ->
(p + 8 <= b + N \/ b + N + K <= p) ->
(p + 8 <= D \/ D + K <= p) ->
(b + N + K <= D \/ D + K <= b + N) ->
val_mem SEGS (mrestrict (w_H W) memc) p 8 N ->
garr8 SEGS (mrestrict (w_H W) memc) D pre ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x2304)) memc (seg_rom SEGS)) mdc)
(fun W' c' => W' = W /\ exists regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + 0x2398)) mem' (seg_rom SEGS)) md' /\
ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc Sc W mem' md' ev /\
(forall r, In r PD_CL_KEPT -> getr regs' r = getr regs r) /\
garr8 SEGS (mrestrict (w_H W) mem') (b + N) (rev pre) /\
val_mem SEGS (mrestrict (w_H W) mem') p 8 (N + K) /\
garr8 SEGS (mrestrict (w_H W) mem') D pre /\
(forall a, 0 <= a < 2 ^ 64 -> ~ (p <= a < p + 8) -> ~ (b + N <= a < b + N + K) ->
aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
(forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
intros pre W regs memc mdc STK sp0 ev FP ly S W0 mem0 md0 own pos lyc Sc p b N D K
HlenK HK10 HJ Hfr HD Hb0 HN0 Hp8 R14 R15 R16 R18 R19 R22 HWP HWB HSP HSB HRD Hdj1 Hdj2 Hdj3 HVP HGD.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as HCR. unfold YG0f.ASAN_CEIL in HCR.
pose proof (proj1 HJ) as HAR.
destruct (frames_bounds SEGS B LAWS lyc Sc W memc mdc 0 pos HAR Hfr) as (HF4096 & HFceil & HFapp).
assert (HFB : fs_frame_bytes 0 = 64) by reflexivity. rewrite HFB in HFceil.
pose proof HSP as (HSP1 & HSP2 & HSP4 & HSP5 & HSP6).
pose proof HSB as (HSB1 & HSB2 & HSB4 & HSB5 & HSB6).
assert (HPhi : p + 8 <= 2 ^ 47 - 1)
by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HSP4; lia).
assert (HBhi : b + N + K <= 2 ^ 47 - 1)
by (unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in HSB4; lia).
assert (HDhi : D + K <= 2 ^ 47 - 2) by lia.
assert (R15' : getr regs 15 = w64 (18446744073709551615 - D))
by (rewrite R15, lxor_allones by lia; reflexivity).
remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E14 : ew E 14 = Z_to_bv 64 D) by (rewrite (EE 14%nat 14%bv eq_refl); exact R14).
assert (E15 : ew E 15 = Z_to_bv 64 (18446744073709551615 - D)) by (rewrite (EE 15%nat 15%bv eq_refl); exact R15').
assert (E16 : ew E 16 = Z_to_bv 64 K) by (rewrite (EE 16%nat 16%bv eq_refl); exact R16).
assert (E18 : ew E 18 = Z_to_bv 64 p) by (rewrite (EE 18%nat 18%bv eq_refl); exact R18).
assert (E19 : ew E 19 = Z_to_bv 64 b) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E22 : ew E 22 = Z_to_bv 64 SB) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (HS : st_ok_pi SEGS VAL E cl_ssu
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x2304)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold cl_ssu. apply pa_entry_st_ok_full.
- rewrite HE. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- cbn [pairwise_disjoint]. exact I.
- split; [|split; [exact I | exact I]].
cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite E22, unsigned_lit_small by (unfold SB; lia).
rewrite Z.pow_0_r, Z.mod_1_r. repeat split; try exact I; lia. }
assert (SHOK : sh_ok SEGS cl_Bx (@nil shent) E (mrestrict (w_H W) memc)) by apply Forall_nil.
clear HE.
paj_run_to_tok RUNTO HS HJ SHOK Bspan 0x231c. { apply awr_ok_nil. }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ PD_CL_KEPT HS ltac:(env_agree_chain HAE)
ltac:(vm_compute; reflexivity)) as HK.
cbn [ms_regs restrict] in HK.
prregR HS (5%bv : bv 5) N5. prregR HS (6%bv : bv 5) N6. prregR HS (7%bv : bv 5) N7.
prregR HS (16%bv : bv 5) N16. prregR HS (17%bv : bv 5) N17.
lazymatch type of N16 with _ = sv_denot ?Ex _ =>
rewrite (cl_denot_of_U Ex _ _ (U_atom_off Ex 16 K (-1)
ltac:(rewrite ?ew_ewset_other by lia; exact E16) ltac:(lia) ltac:(lia))) in N16 end.
lazymatch type of N17 with _ = sv_denot ?Ex _ =>
rewrite (cl_denot_of_U Ex _ _ (U_not Ex 19 b
ltac:(rewrite ?ew_ewset_other by lia; exact E19) ltac:(lia))) in N17 end.
lazymatch type of N6 with _ = sv_denot ?Ex _ =>
rewrite (denot_shx Ex 18 22 0 p SB
ltac:(rewrite ?ew_ewset_other by lia; exact E18)
ltac:(rewrite ?ew_ewset_other by lia; exact E22) ltac:(lia) ltac:(lia) ltac:(lia)
ltac:(unfold SB; lia)) in N6 end.
rewrite Z.add_0_r in N6. cbn [sv_denot] in N5, N7.
assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) _ _ _ _ _ (fun _ => False) HFr
ltac:(intros bq wlo whi x Hin Hrr; vm_compute in Hin; destruct Hin)); [exact Ha | intros []]. }
assert (KEEP0B : forall s, SHADOW_OFF <= s < kHighShadowEnd ->
aview SEGS (w_H W) (ms_mem ms) s = aview SEGS (w_H W) memc s)
by (intros s Hs; apply KEEP0; unfold SHADOW_OFF, kHighShadowEnd in Hs; lia).
pmkst HS.
eapply SRr_mono.
{ eapply (pd_cl_loop (length pre) pre [] W (ms_regs ms) (ms_mem ms) _ STK sp0 ev FP ly S W0 mem0 md0
own pos lyc Sc p b N D 0 K).
- reflexivity.
- exact HlenK.
- lia.
- lia.
- lia.
- exact HJ.
- exact Hfr.
- exact HD.
- exact Hb0.
- exact HN0.
- exact Hp8.
- cbn [ms_regs]. rewrite N5. reflexivity.
- cbn [ms_regs]. rewrite N6. reflexivity.
- cbn [ms_regs]. rewrite N7. reflexivity.
- cbn [ms_regs]. rewrite (HK 14%bv ltac:(cbv; tauto)). exact R14.
- cbn [ms_regs]. rewrite (HK 15%bv ltac:(cbv; tauto)). exact R15'.
- cbn [ms_regs]. rewrite N16. unfold w64. f_equal; lia.
- cbn [ms_regs]. rewrite N17. unfold w64. f_equal; lia.
- cbn [ms_regs]. rewrite (HK 18%bv ltac:(cbv; tauto)). exact R18.
- cbn [ms_regs]. rewrite (HK 19%bv ltac:(cbv; tauto)). exact R19.
- cbn [ms_regs]. rewrite (HK 22%bv ltac:(cbv; tauto)). exact R22.
- unfold spZ. cbn [ms_regs]. rewrite (HK 2%bv ltac:(cbv; tauto)).
intros a Ha. destruct (HWP a Ha) as (HA1 & HA2 & HA3 & HA4).
split; [exact HA1|]. split; [exact (apresent_grows (w_H W) memc (ms_mem ms) a HG HA2)|].
split; [exact HA3 | exact HA4].
- unfold spZ. cbn [ms_regs]. rewrite (HK 2%bv ltac:(cbv; tauto)).
intros a Ha. destruct (HWB a ltac:(lia)) as (HA1 & HA2 & HA3 & HA4).
split; [exact HA1|]. split; [exact (apresent_grows (w_H W) memc (ms_mem ms) a HG HA2)|].
split; [exact HA3 | exact HA4].
- unfold spZ. cbn [ms_regs]. rewrite (HK 2%bv ltac:(cbv; tauto)).
split; [|split; [|split; [exact HSP4 | split; [exact HSP5 | exact HSP6]]]].
+ intros a Ha. split; [|exact (proj2 (HSP1 a Ha))].
rewrite (KEEP0 a ltac:(lia)). exact (proj1 (HSP1 a Ha)).
+ apply (cl_ra_band _ _ p 8 KEEP0B); [lia | lia | exact HSP2].
- unfold spZ. cbn [ms_regs]. rewrite (HK 2%bv ltac:(cbv; tauto)).
split; [|split; [|split; [|split]]].
+ intros a Ha. split; [|exact (proj2 (HSB1 a ltac:(lia)))].
rewrite (KEEP0 a ltac:(lia)). exact (proj1 (HSB1 a ltac:(lia))).
+ apply (cl_ra_band _ _ (b + N) (0 + K) KEEP0B); [lia | lia|].
rewrite Z.add_0_l. exact HSB2.
+ rewrite Z.add_0_l. exact HSB4.
+ lia.
+ lia.
- apply (cl_ra_band _ _ D K KEEP0B); [lia | lia | exact HRD].
- lia.
- lia.
- lia.
- cbn [ms_mem]. rewrite Z.add_0_r.
apply (cl_val_mem_kept _ memc); [intros x Hx; apply KEEP0; lia | exact HVP].
- apply garr8_nil.
- cbn [ms_mem]. apply (cl_garr8_kept _ memc); [intros x Hx; apply KEEP0; lia | exact HGD]. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ4 & HK3 & GB3 & VP3 & GD3 & KP3 & GR3).
split; [reflexivity|]. exists regs3, mem3, md3. split; [reflexivity|]. split; [exact HJ4|].
split.
{ intros r Hr. rewrite (HK3 r ltac:(revert Hr; unfold PD_CL_KEPT, PD_CLB_KEPT; cbn [In]; tauto)).
cbn [ms_regs]. exact (HK r Hr). }
split; [cbn [app] in GB3; exact GB3|].
split; [rewrite Z.add_0_r in VP3; exact VP3|].
split; [exact GD3|].
split.
{ intros a Ha Hn1 Hn2. rewrite (KP3 a Ha Hn1 ltac:(lia)). apply KEEP0. exact Ha. }
{ intros a Hpr. apply GR3. exact (apresent_grows (w_H W) memc (ms_mem ms) a HG Hpr). }
Qed.

(* ---- Tail ---- *)
Lemma pd_tail :
  forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k (regs regs0 : bvmap 5 word) (pos : Z),
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc Sc W memc mdc k ->
  YK0s.ret_ok (getr regs0 1) ->
  getr regs 3 = getr regs0 3 -> getr regs 4 = getr regs0 4 ->
  getr regs 8 = Z_to_bv 64 (spZ regs0) ->
  getr regs 10 = w64 (frame_addr lyc 0 pos) -> getr regs 12 = w64 (frame_addr lyc 0 pos) ->
  getr regs 13 = w64 (SB + frame_addr lyc 0 pos / 8) ->
  getr regs 23 = getr regs0 23 -> getr regs 24 = getr regs0 24 -> getr regs 25 = getr regs0 25 ->
  getr regs 26 = getr regs0 26 -> getr regs 27 = getr regs0 27 ->
  rdword (aview SEGS (w_H W) memc) (frame_addr lyc 0 pos + 56) = Some (flag_addr lyc 0 pos) ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs0 - 8) 8 (bv_unsigned (getr regs0 1)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs0 - 16) 8 (bv_unsigned (getr regs0 8)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs0 - 24) 8 (bv_unsigned (getr regs0 9)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs0 - 32) 8 (bv_unsigned (getr regs0 18)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs0 - 40) 8 (bv_unsigned (getr regs0 19)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs0 - 48) 8 (bv_unsigned (getr regs0 20)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs0 - 56) 8 (bv_unsigned (getr regs0 21)) ->
  val_mem SEGS (mrestrict (w_H W) memc) (spZ regs0 - 64) 8 (bv_unsigned (getr regs0 22)) ->
  sp0 - STK <= spZ regs0 - 96 ->
  SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + 0x2398)) memc (seg_rom SEGS)) mdc)
  (fun W' c' => W' = W /\ exists regs' mem' md',
     c' = mkCfg (mkst regs' (getr regs0 1) mem' (seg_rom SEGS)) md' /\
     ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc (stack_free_state 0 pos Sc) W mem' md' k /\
     aregs_preserved regs0 regs' /\
     frames Sc = (0, pos) :: frames (stack_free_state 0 pos Sc) /\
     ablocks B lyc (stack_free_state 0 pos Sc) = ablocks B lyc Sc /\
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64) ->
        ~ (SB + frame_addr lyc 0 pos / 8 <= a < SB + frame_addr lyc 0 pos / 8 + 8) ->
        a <> flag_addr lyc 0 pos ->
        aview SEGS (w_H W) mem' a = aview SEGS (w_H W) memc a) /\
     (forall a, apresent (w_H W) memc a -> apresent (w_H W) mem' a)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs regs0 pos
HJ Hra G3 G4 G8 G10 G12 G13 G23 G24 G25 G26 G27 Hflag V1 V8 V9 V18 V19 V20 V21 V22 Hwlo.
unfold YK0s.ret_ok in Hra. pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HJ as (HAR & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HST & _).
assert (Hin : In (0, pos) (frames Sc)) by (rewrite Hfrs; left; reflexivity).
destruct HST as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
destruct (al_frames _ _ LAWS _ _ _ _ _ 0 pos HAR Hin) as (_ & _ & HFpres & HFSpres).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ 0 pos HAR Hin) as (HF4096 & HFceil & HFapp).
destruct (al_flag _ _ LAWS _ _ _ _ _ 0 pos HAR Hin) as (HFLpres & HFLown & HFLapp & HFLceil).
change (fs_frame_bytes 0) with 64 in HFpres, HFSpres, HFceil, HFapp.
change (64 / 8) with 8 in HFSpres.
unfold in_app, kLowShadowBeg, kHighMemBeg in HFLapp, HFapp.
set (F := frame_addr lyc 0 pos) in *. set (FL := flag_addr lyc 0 pos) in *.
assert (HFLF : ~ (F <= FL < F + 64)) by (intros Hx; exact (proj2 (HFpres FL Hx) HFLown)).
assert (HSBF : shadow_addr F = SB + F / 8) by (unfold shadow_addr, SB, SHADOW_OFF; lia).
assert (HF8lo : 512 <= F / 8) by (apply Z.div_le_lower_bound; lia).
assert (HF8hi : F / 8 < 17592186044416 - 7) by (apply Z.div_lt_upper_bound; lia).
assert (Hsp : 0 <= spZ regs0 < 2 ^ 64).
{ unfold spZ. pose proof (bv_unsigned_in_range 64 (getr regs0 2)) as Hr.
  change (bv_modulus 64) with (2 ^ 64) in Hr. exact Hr. }
assert (RG : forall r, 0 <= bv_unsigned (getr regs0 r) < 2 ^ (8 * Z.of_N 8)).
{ intros r. pose proof (bv_unsigned_in_range 64 (getr regs0 r)) as Hr.
  change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr. exact Hr. }
remember (Eimg (Ereg regs [Z_to_bv 64 FL; getr regs0 1; getr regs0 8; getr regs0 9; getr regs0 18;
  getr regs0 19; getr regs0 20; getr regs0 21; getr regs0 22])) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (rewrite HE; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; rewrite HE; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E8 : ew E 8 = Z_to_bv 64 (spZ regs0)) by (rewrite (EE 8%nat 8%bv eq_refl); exact G8).
assert (E12 : ew E 12 = Z_to_bv 64 F) by (rewrite (EE 12%nat 12%bv eq_refl); exact G12).
assert (E13 : ew E 13 = Z_to_bv 64 (SB + F / 8)) by (rewrite (EE 13%nat 13%bv eq_refl); exact G13).
assert (E32 : ew E 32 = Z_to_bv 64 FL)
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = getr regs0 1)
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = getr regs0 8)
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = getr regs0 9)
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E36 : ew E 36 = getr regs0 18)
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
assert (E37 : ew E 37 = getr regs0 19)
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 5)).
assert (E38 : ew E 38 = getr regs0 20)
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 6)).
assert (E39 : ew E 39 = getr regs0 21)
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 7)).
assert (E40 : ew E 40 = getr regs0 22)
by (rewrite HE, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 8)).
assert (U8 : bv_unsigned (ew E 8) = spZ regs0) by (rewrite E8; apply unsigned_lit_small; exact Hsp).
assert (U12 : bv_unsigned (ew E 12) = F) by (rewrite E12; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = SB + F / 8) by (rewrite E13; apply unsigned_lit_small; unfold SB; lia).
assert (U32 : bv_unsigned (ew E 32) = FL) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HS : st_ok_pi SEGS VAL E pt_ss
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + 0x2398)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pt_ss. apply pa_entry_st_ok_full.
  - unfold pt_regs. apply regs_ok_pin; [rewrite HE; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
    cbn [sv_denot]. rewrite E12, Z.add_0_r, Z_to_bv_bv_unsigned. exact G10.
  - vm_compute. reflexivity.
  - unfold pt_mem. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U12. split; [lia|]. split; [lia|]. split.
      * intros o Ho. apply (apresent_writable SEGS). exact (proj1 (HFpres (F + o) ltac:(lia))).
      * constructor; [|constructor].
        apply (chunk_ok_val SEGS E _ F 56 8 (SOff 32 0) FL);
        [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
        exact (val_mem_of_rdword SEGS (w_H W) memc _ _ Hflag).
    + rewrite U13. split; [unfold SB; lia|]. split; [unfold SB; lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). rewrite <- HSBF. exact (proj1 (HFSpres o ltac:(lia))).
    + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable SEGS). replace (FL + o) with FL by lia. exact HFLpres.
    + rewrite U8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ (spZ regs0) (-8) 8 (SOff 33 0) (bv_unsigned (getr regs0 1)));
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; reflexivity | apply RG | cbn; lia |].
        replace (spZ regs0 + -8) with (spZ regs0 - 8) by lia. exact V1.
      * apply (chunk_ok_val SEGS E _ (spZ regs0) (-16) 8 (SOff 34 0) (bv_unsigned (getr regs0 8)));
        [cbn [sv_denot]; rewrite E34, Z.add_0_r; reflexivity | apply RG | cbn; lia |].
        replace (spZ regs0 + -16) with (spZ regs0 - 16) by lia. exact V8.
      * apply (chunk_ok_val SEGS E _ (spZ regs0) (-24) 8 (SOff 35 0) (bv_unsigned (getr regs0 9)));
        [cbn [sv_denot]; rewrite E35, Z.add_0_r; reflexivity | apply RG | cbn; lia |].
        replace (spZ regs0 + -24) with (spZ regs0 - 24) by lia. exact V9.
      * apply (chunk_ok_val SEGS E _ (spZ regs0) (-32) 8 (SOff 36 0) (bv_unsigned (getr regs0 18)));
        [cbn [sv_denot]; rewrite E36, Z.add_0_r; reflexivity | apply RG | cbn; lia |].
        replace (spZ regs0 + -32) with (spZ regs0 - 32) by lia. exact V18.
      * apply (chunk_ok_val SEGS E _ (spZ regs0) (-40) 8 (SOff 37 0) (bv_unsigned (getr regs0 19)));
        [cbn [sv_denot]; rewrite E37, Z.add_0_r; reflexivity | apply RG | cbn; lia |].
        replace (spZ regs0 + -40) with (spZ regs0 - 40) by lia. exact V19.
      * apply (chunk_ok_val SEGS E _ (spZ regs0) (-48) 8 (SOff 38 0) (bv_unsigned (getr regs0 20)));
        [cbn [sv_denot]; rewrite E38, Z.add_0_r; reflexivity | apply RG | cbn; lia |].
        replace (spZ regs0 + -48) with (spZ regs0 - 48) by lia. exact V20.
      * apply (chunk_ok_val SEGS E _ (spZ regs0) (-56) 8 (SOff 39 0) (bv_unsigned (getr regs0 21)));
        [cbn [sv_denot]; rewrite E39, Z.add_0_r; reflexivity | apply RG | cbn; lia |].
        replace (spZ regs0 + -56) with (spZ regs0 - 56) by lia. exact V21.
      * apply (chunk_ok_val SEGS E _ (spZ regs0) (-64) 8 (SOff 40 0) (bv_unsigned (getr regs0 22)));
        [cbn [sv_denot]; rewrite E40, Z.add_0_r; reflexivity | apply RG | cbn; lia |].
        replace (spZ regs0 + -64) with (spZ regs0 - 64) by lia. exact V22.
  - unfold pt_mem. cbn [pairwise_disjoint all_disjoint].
    repeat match goal with |- _ /\ _ => split end;
    first [ exact I
    | unfold extent_disjoint; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
      rewrite ?U8, ?U12, ?U13, ?U32; unfold SB; lia ].
  - split; [|split; [exact I | exact I]].
    unfold pt_facts. cbn [f_atoms atoms_ok]. unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U12, Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia. }
clear HE.
paj_run_flag_sh RUNF HS HJ.
- lia.
- intros a (r & Hr0 & Hr).
  lazymatch type of Hr0 with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr0 end.
  destruct Hr0 as [<- | [<- | [<- | [<- | []]]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U8, ?U12, ?U13, ?U32 in Hr.
  + left. right; right; right. exists 0, pos. split; [left; reflexivity|].
    left. unfold in_zr; cbn [fst snd]. fold F. change (fs_frame_bytes 0) with 64. lia.
  + left. right; right; right. exists 0, pos. split; [left; reflexivity|].
    right. unfold in_zr; cbn [fst snd]. fold F. rewrite HSBF. change (fs_frame_bytes 0 / 8) with 8. lia.
  + right. fold FL. lia.
  + exfalso. lia.
- intros msr HSr.
  pose proof (st_ok_pi_region_nth E _ msr 2%nat _ HSr eq_refl) as HR.
  pose proof (field_of_region E (ms_mem msr) 32 FL _ 0 1 0 1 0 1%N (SLit 0) 0 HR U32
    ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0. exact V0.
- cbn [ms_mem mkst] in HF, HFr, HG.
  prreg HS (1%bv : bv 5) R1.
  assert (R1' : v_jalr (getr (ms_regs ms) 1) 0 = getr regs0 1) by (rewrite R1, E33; exact Hra).
  assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (F <= a < F + 64) -> ~ (SB + F / 8 <= a < SB + F / 8 + 8) ->
    a <> FL -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) memc a).
  { intros a Ha Hf Hs Hfl.
    apply (kept_of_frame E _ (w_H W) memc (ms_mem ms)
      (fun x => (F <= x < F + 64) \/ (SB + F / 8 <= x < SB + F / 8 + 8) \/ x = FL) HFr);
    [| exact Ha | intros [HH | [HH | HH]]; [exact (Hf HH) | exact (Hs HH) | exact (Hfl HH)]].
    intros bb wlo whi aa Hw Hr. vm_compute in Hw.
    repeat (destruct Hw as [Eq | Hw]; [injection Eq as <- <- <-; cbn [base_val] in Hr;
      rewrite ?U8, ?U12, ?U13, ?U32 in Hr; lia |]).
    destruct Hw. }
  assert (GROW : forall a, apresent (w_H W) memc a -> apresent (w_H W) (ms_mem ms) a)
  by (intros a Hp; eapply apresent_grows; [exact HG | exact Hp]).
  pose proof HJ as (_ & _ & _ & _ & _ & Hfrs2 & _).
  eapply (RET W E _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbv beta. rewrite R1'.
  split; [reflexivity|]. do 3 eexists. split; [reflexivity|].
  split; [apply (ajournal_materialize SEGS B LAWS Hsegs); exact HJ|].
  split.
  { apply aregs_preserved_eqs;
    lazymatch goal with |- getr (ms_regs ?m) ?r = _ =>
      let T := fresh "T" in prreg HS r T; rewrite T; clear T end;
    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned.
    - rewrite E8. unfold spZ. apply Z_to_bv_bv_unsigned.
    - rewrite (EE 3%nat 3%bv eq_refl). exact G3.
    - rewrite (EE 4%nat 4%bv eq_refl). exact G4.
    - exact E34.
    - exact E35.
    - exact E36.
    - exact E37.
    - exact E38.
    - exact E39.
    - exact E40.
    - rewrite (EE 23%nat 23%bv eq_refl). exact G23.
    - rewrite (EE 24%nat 24%bv eq_refl). exact G24.
    - rewrite (EE 25%nat 25%bv eq_refl). exact G25.
    - rewrite (EE 26%nat 26%bv eq_refl). exact G26.
    - rewrite (EE 27%nat 27%bv eq_refl). exact G27. }
  split; [rewrite Hfrs, Hfrs2; reflexivity|].
  split; [unfold ablocks; rewrite blocks_stack_free_state; reflexivity|].
  split; [exact KEEP | exact GROW].
Qed.


Lemma pd_map_unsig : forall l, (forall j, (j < length l)%nat -> 0 <= nth j l 0 < 256) ->
  map bv_unsigned (map (Z_to_bv 8) l) = l.
Proof.
induction l as [|z l IH]; cbn [map]; intros H; [reflexivity|].
f_equal.
- rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  apply Z.mod_small. exact (H 0%nat ltac:(cbn [length]; lia)).
- apply IH. intros j Hj. exact (H (S j) ltac:(cbn [length]; lia)).
Qed.

Lemma pd_nth_firstn : forall {X} (l : list X) kk j (d : X), (j < kk)%nat -> nth j (firstn kk l) d = nth j l d.
Proof.
intros X l. induction l as [|a l IH]; intros kk j d Hj.
- destruct kk; cbn [firstn]; destruct j; reflexivity.
- destruct kk as [|kk]; [lia|]. cbn [firstn]. destruct j as [|j]; cbn [nth];
  [reflexivity | apply IH; lia].
Qed.

Lemma pd_garr8_firstn : forall (m : word -> option byte) base l kk,
  garr8 SEGS m base l -> garr8 SEGS m base (firstn kk l).
Proof.
intros m base l kk H j Hj. rewrite length_firstn in Hj.
rewrite (pd_nth_firstn l kk j 0) by lia. apply H. lia.
Qed.

Lemma pd_pres_of_view : forall (W : world SEGS) (m m' : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img SEGS a ->
  aview SEGS (w_H W) m' a = aview SEGS (w_H W) m a ->
  apresent (w_H W) m a -> apresent (w_H W) m' a.
Proof.
intros W m m' a Ha Hni Heq (Hh & bb & Hb). split; [exact Hh|].
unfold aview, mbyte, mrestrict in Heq. rewrite Hh, Hb in Heq.
rewrite (seg_rom_none SEGS a Ha Hni) in Heq.
destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | cbn in Heq; discriminate].
Qed.

Lemma pd_flag_off_img : forall ly S (W : world SEGS) mem md cid pos,
  AR SEGS B ly S W mem md -> 0 <= cid <= 10 -> 0 <= pos < fs_frames cid ->
  ~ in_img SEGS (flag_addr ly cid pos).
Proof.
intros ly S W mem md cid pos HAR Hc Hp Hi.
pose proof (pa_img_range _ Hi) as Hr.
pose proof HAR as (M & LG & _). pose proof (am_layout _ _ _ _ M) as LO.
pose proof (pa_img_cover ly S md LG) as (C1 & C2).
pose proof (lo_disj _ LO) as HD.
cbv [static_extents owned_extents] in HD. cbn [app pairwise] in HD.
destruct HD as (_ & _ & _ & HF & _).
rewrite Forall_forall in HF.
pose proof (HF (ly_img ly) ltac:(cbn [In]; repeat (first [solve [left; reflexivity] | right]))) as HDisj.
unfold zdisjoint in HDisj. cbn [fst snd] in HDisj.
pose proof (flag_off_bounds cid pos Hc Hp) as Hoff.
unfold flag_addr in *. unfold kFakeFlagsOff, kFakeFramesOff, kFakeStackSize in *.
lia.
Qed.

Lemma pd_caller_sep : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem2 md2 pos a,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR SEGS B lyc S2 W mem2 md2 ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  frames S2 = (0, pos) :: frames Sc ->
  0 <= pos < fs_frames 0 ->
  awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a ->
  ~ (frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64) /\
  ~ (SB + frame_addr lyc 0 pos / 8 <= a < SB + frame_addr lyc 0 pos / 8 + 8) /\
  a <> flag_addr lyc 0 pos /\ ~ in_img SEGS a.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem2 md2 pos a
HJ HAR2 Eab Hfrs2 Hpos HW.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HST & _).
destruct HST as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 0 pos HAR2 Hin2) as (HF4096 & HFceil & HFapp).
pose proof (frm_off_imgP B lyc S2 W mem2 md2 0 pos HAR2 Hin2) as HFimg.
destruct (FFL lyc S2 W mem2 md2 0 pos HAR2 Hin2) as (HFLpres & HFLown & HFLapp & HFLceil).
pose proof (pd_flag_off_img lyc S2 W mem2 md2 0 pos HAR2 ltac:(lia) Hpos) as HFLimg.
change (fs_frame_bytes 0) with 64 in HFceil, HFapp.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc 0 pos) ltac:(lia)) as HSB1.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc 0 pos + 64) ltac:(lia)) as HSB2.
assert (HSBF : shadow_addr (frame_addr lyc 0 pos) = SB + frame_addr lyc 0 pos / 8)
  by (unfold shadow_addr, SB, SHADOW_OFF; lia).
pose proof (shadow_range_end (frame_addr lyc 0 pos) 64 ltac:(lia)) as Hre.
change (64 / 8) with 8 in Hre.
change (fs_frame_bytes 0) with 64 in *.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJ HW)
  as (_ & [[Hc Hst] | [(Happ & b0 & m0 & Hin & Hr & _) | (cid & pos' & Hin & Hcase)]]).
- split; [lia|]. split; [unfold kLowMemEnd, kHighShadowEnd in *; lia|].
  split; [lia|]. intros Hi. pose proof (pa_img_range _ Hi). lia.
- assert (Hinb : In (b0, m0) (ablocks B lyc S2)) by (rewrite Eab; exact Hin).
  destruct (al_blocks _ _ LAWS lyc S2 W mem2 md2 b0 m0 HAR2 Hinb) as (_ & H4096 & Hce & Happ2 & Hbp & _).
  pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 b0 m0 0 pos HAR2 Hinb Hin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_zr in Hr. cbn [fst snd] in Hr.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ2.
  split; [lia|].
  split; [rewrite <- HSBF; intros Hx; unfold kLowMemEnd, kHighShadowEnd in *; lia|].
  split.
  + intros ->. exact (proj2 (Hbp (flag_addr lyc 0 pos) ltac:(lia)) HFLown).
  + pose proof (blk_off_imgP B lyc S2 W mem2 md2 b0 m0 HAR2 Hinb) as Hoff.
    intros Hi. pose proof (pa_img_range _ Hi). lia.
- assert (HinSc : In (cid, pos') (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  assert (HinS2 : In (cid, pos') (frames S2)) by (rewrite Hfrs2; right; exact HinSc).
  destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 cid pos' HAR2 HinS2) as (_ & _ & Hfp & Hfs).
  assert (Hdj : (in_zr a (frame_rng lyc (0, pos)) \/
                 in_zr a (shadow_addr (frame_addr lyc 0 pos), fs_frame_bytes 0 / 8)) -> False).
  { intros Hr2. apply in_split in HinSc as (l1 & l2 & El).
    apply (frames_zone_disj SEGS B LAWS lyc S2 W mem2 md2 (0, pos) (cid, pos') [] l1 l2 a HAR2);
    [rewrite Hfrs2, El; reflexivity | cbn [fst snd]; exact Hr2
    | cbn [fst snd]; destruct Hcase as [(_ & Hz1) | (_ & Hz1)]; [left; exact Hz1 | right; exact Hz1]]. }
  split; [intros Hx; apply Hdj; left; unfold frame_rng, in_zr; cbn [fst snd];
          change (fs_frame_bytes 0) with 64; lia|].
  split; [intros Hx; apply Hdj; right; unfold in_zr; cbn [fst snd]; rewrite HSBF;
          change (fs_frame_bytes 0) with 64; change (64 / 8) with 8; lia|].
  destruct Hcase as [Hzr | Hzr].
  + unfold in_zr, frame_rng in Hzr. cbn [fst snd] in Hzr.
    split.
    * intros ->. exact (proj2 (Hfp (flag_addr lyc 0 pos) ltac:(lia)) HFLown).
    * pose proof (frm_off_imgP B lyc S2 W mem2 md2 cid pos' HAR2 HinS2) as Hoff.
      destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 cid pos' HAR2 HinS2) as (Hc1 & Hc2 & Hc3).
      intros Hi. pose proof (pa_img_range _ Hi). lia.
  + unfold in_zr in Hzr. cbn [fst snd] in Hzr.
    assert (Hi8 : 0 <= a - shadow_addr (frame_addr lyc cid pos') < fs_frame_bytes cid / 8) by lia.
    split.
    * intros ->. apply (proj2 (Hfs _ Hi8)).
      replace (shadow_addr (frame_addr lyc cid pos') + (flag_addr lyc 0 pos - shadow_addr (frame_addr lyc cid pos')))
        with (flag_addr lyc 0 pos) by lia. exact HFLown.
    * intros Hi. pose proof (pa_img_range _ Hi).
      pose proof (YCbq.shadow_addr_bounds (frame_addr lyc cid pos') ltac:(
        destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 cid pos' HAR2 HinS2) as (Hc1 & _ & _); lia)) as Hsb.
      unfold SHADOW_OFF in *. lia.
Qed.


Lemma pd_not_word : forall x, 0 <= x < 2 ^ 63 ->
  Z_to_bv 64 (- x - 1) = w64 (Z.lxor x 18446744073709551615).
Proof.
intros x Hx. replace 18446744073709551615 with (2 ^ 64 - 1) by reflexivity.
rewrite (lxor_allones x ltac:(lia)). unfold w64. apply bv_eq.
rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
rewrite <- (Z.mod_add (- x - 1) 1 (2 ^ 64)) by lia. f_equal. lia.
Qed.

Lemma pd_garr8_kept : forall (W : world SEGS) (m m' : word -> option byte) base l,
  (forall kk, 0 <= kk < Z.of_nat (length l) ->
     aview SEGS (w_H W) m' (base + kk) = aview SEGS (w_H W) m (base + kk)) ->
  garr8 SEGS (mrestrict (w_H W) m) base l -> garr8 SEGS (mrestrict (w_H W) m') base l.
Proof.
intros W m m' base l HK HG j Hj. destruct (HG j Hj) as (HV & HB). split; [|exact HB].
apply (val_mem_kept SEGS (w_H W) (w_H W) m m'); [|exact HV].
intros kk Hk. cbn [Z.of_nat] in Hk.
replace (base + Z.of_nat j + kk) with (base + (Z.of_nat j + kk)) by lia.
apply HK. lia.
Qed.

(* The caller's write rights, carried from the entry state to a later state of the walk. *)
Lemma pd_twr_inner : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  S2 mem3 md3 pos sp q n,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem3 md3 k ->
  frames S2 = (0, pos) :: frames Sc ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - PUT_DEC_STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W) mem3 a) ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc sp q n ->
  (q + n <= sp - PUT_DEC_STK \/ sp <= q) ->
  twr_ok B STK sp0 FP ly S lyc S2 ((0, pos) :: own) W mem3 (sp - 96) q n.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem3 md3 pos sp q n
HJc HJ3 Hfrs2 Eab HPG HWR Hside.
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSTK : PUT_DEC_STK = 4208) by reflexivity.
pose proof (proj1 HJ3) as HAR3.
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HST & _).
destruct HST as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
intros a Ha. destruct (HWR a Ha) as (HA1 & HA2 & HA3 & HA4).
destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJc HA1)
  as (_ & Hloc).
assert (HA1' : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc S2) lyc ((0, pos) :: own) a).
{ rewrite Eab. destruct HA1 as [H1 | [H1 | [H1 | H1]]];
  [left; exact H1 | right; left; exact H1 | right; right; left; exact H1 | ].
  right; right; right. destruct H1 as (cid & pos' & Hin & Hr).
  exists cid, pos'. split; [right; exact Hin | exact Hr]. }
split; [exact HA1'|].
split.
{ destruct Hloc as [[Hc Hst] | [(Happ & b0 & m0 & Hin & Hr & _) | (cid & pos' & Hin & Hcase)]].
  - apply HPG; [lia | lia | exact HA2].
  - assert (Hinb : In (b0, m0) (ablocks B lyc S2)) by (rewrite Eab; exact Hin).
    destruct (al_blocks _ _ LAWS lyc S2 W mem3 md3 b0 m0 HAR3 Hinb) as (_ & _ & _ & _ & Hbp & _).
    exact (proj1 (Hbp a ltac:(unfold in_zr in Hr; cbn [fst snd] in Hr; lia))).
  - assert (HinS2 : In (cid, pos') (frames S2)).
    { rewrite Hfrs2. right. rewrite Hfrs. apply in_or_app. left. exact Hin. }
    destruct (al_frames _ _ LAWS lyc S2 W mem3 md3 cid pos' HAR3 HinS2) as (_ & _ & Hfp & Hfs).
    destruct Hcase as [(_ & Hzr) | (_ & Hzr)].
    + unfold in_zr, frame_rng in Hzr. cbn [fst snd] in Hzr.
      exact (proj1 (Hfp a ltac:(lia))).
    + unfold in_zr in Hzr. cbn [fst snd] in Hzr.
      pose proof (proj1 (Hfs (a - shadow_addr (frame_addr lyc cid pos')) ltac:(lia))) as HX.
      replace (shadow_addr (frame_addr lyc cid pos') + (a - shadow_addr (frame_addr lyc cid pos')))
        with a in HX by lia. exact HX. }
split.
{ destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem3 md3 k a
    HJ3 HA1') as (Hnown & _). exact Hnown. }
lia.
Qed.


Lemma pd_skipn_map : forall {X Y} (f : X -> Y) n l, map f (skipn n l) = skipn n (map f l).
Proof.
intros X Y f n. induction n as [|n IH]; intros l; [reflexivity|].
destruct l as [|a l]; [reflexivity|]. cbn [skipn map]. apply IH.
Qed.

Lemma pd_firstn_map : forall {X Y} (f : X -> Y) n l, map f (firstn n l) = firstn n (map f l).
Proof.
intros X Y f n. induction n as [|n IH]; intros l; [reflexivity|].
destruct l as [|a l]; [reflexivity|]. cbn [firstn map]. f_equal. apply IH.
Qed.

Lemma pd_firstn_app_exact : forall {X} (l1 l2 : list X), firstn (length l1) (l1 ++ l2) = l1.
Proof.
intros X l1. induction l1 as [|a l1 IH]; intros l2; cbn [length firstn app]; [reflexivity|].
f_equal. apply IH.
Qed.

Lemma pd_rev_repeat : forall {X} (x : X) n, rev (repeat x n) = repeat x n.
Proof.
intros X x n. induction n as [|n IH]; [reflexivity|].
cbn [repeat rev]. rewrite IH.
clear IH. induction n as [|n IH]; cbn [repeat app]; [reflexivity|]. f_equal. exact IH.
Qed.

(* A shadow cell of a range the caller may write, re-derived at a later state of the walk. *)
Lemma pd_cell_at : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  S2 mem2 md2 sp q nn x,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  AR SEGS B lyc S2 W mem2 md2 ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (forall cid pos' a, In (cid, pos') (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos')) \/
      in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) memc a) ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc sp q nn ->
  tsrc_ok W memc sp q nn ->
  q <= x < q + nn ->
  exists s, aview SEGS (w_H W) mem2 (shadow_of_addr SHADOW_OFF x) = Some s /\ saddr_ok x s.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem2 md2 sp q nn x
HJ HAR2 Eab KFR HWR HSR Hx.
pose proof (proj1 HJ) as HARc.
pose proof HJ as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & _ & HST & _).
destruct HST as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (proj1 (proj2 HJ)) as Hly.
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
rewrite <- Eslo in Hslo, Hceil. rewrite <- Eshi in Hshi, H47.
destruct HSR as (_ & HRA & _ & HAMR & _ & _).
destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k x HJ
  (proj1 (HWR x Hx))) as (_ & [[Hc Hst] | [(Happ & b0 & m0 & Hin & Hr & _) | (cid & pos' & Hin & Hcase)]]).
- pose proof (al_zshadow _ _ LAWS lyc S2 W mem2 md2 (ly_stk_lo lyc, ly_stk_hi lyc - ly_stk_lo lyc)
    HAR2 ltac:(left; reflexivity)) as HZ. cbn [fst snd] in HZ.
  pose proof HAR2 as (M2 & _). pose proof (am_layout _ _ _ _ M2) as LO.
  pose proof (lo_top _ LO) as (Lb1 & Lb2 & Lb3 & Lb4 & Llo & Lhi & Lb5).
  unfold page_aligned in Llo, Lhi.
  assert (Hlo8 : ly_stk_lo lyc mod 8 = 0).
  { pose proof (Z.div_mod (ly_stk_lo lyc) 4096 ltac:(lia)) as D. rewrite Llo, Z.add_0_r in D.
    rewrite D. replace (4096 * (ly_stk_lo lyc / 4096)) with ((512 * (ly_stk_lo lyc / 4096)) * 8) by lia.
    apply Z_mod_mult. }
  assert (Hhi8 : ly_stk_hi lyc mod 8 = 0).
  { pose proof (Z.div_mod (ly_stk_hi lyc) 4096 ltac:(lia)) as D. rewrite Lhi, Z.add_0_r in D.
    rewrite D. replace (4096 * (ly_stk_hi lyc / 4096)) with ((512 * (ly_stk_hi lyc / 4096)) * 8) by lia.
    apply Z_mod_mult. }
  pose proof (Z.div_mod (ly_stk_lo lyc) 8 ltac:(lia)) as Dlo. rewrite Hlo8, Z.add_0_r in Dlo.
  pose proof (Z.div_mod (ly_stk_hi lyc) 8 ltac:(lia)) as Dhi. rewrite Hhi8, Z.add_0_r in Dhi.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Dxb.
  exists 0. split; [| left; reflexivity].
  replace (shadow_of_addr SHADOW_OFF x)
    with (shadow_of_addr SHADOW_OFF (ly_stk_lo lyc) + (x / 8 - ly_stk_lo lyc / 8))
    by (unfold shadow_of_addr; lia).
  apply HZ.
  assert (Hdiv : (ly_stk_hi lyc - ly_stk_lo lyc) / 8 = ly_stk_hi lyc / 8 - ly_stk_lo lyc / 8).
  { replace (ly_stk_hi lyc - ly_stk_lo lyc) with ((ly_stk_hi lyc / 8 - ly_stk_lo lyc / 8) * 8) by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  rewrite Hdiv.
  set (ql := ly_stk_lo lyc / 8) in *. set (qh := ly_stk_hi lyc / 8) in *.
  set (qx := x / 8) in *. set (xm := x mod 8) in *.
  clearbody ql qh qx xm.
  clear - Dlo Dhi Dx Dxb Hst Hslo Hshi. lia.
- destruct (range_addressable_of_block SEGS B LAWS lyc S2 W mem2 md2 b0 m0 x 1 HAR2
    ltac:(rewrite Eab; exact Hin) ltac:(lia) ltac:(lia) x ltac:(lia)) as (s & Hs & Hok).
  exists s. split; [exact Hs | exact Hok].
- assert (HinSc : In (cid, pos') (frames Sc)) by (rewrite Hfrs; apply in_or_app; left; exact Hin).
  destruct (HRA x Hx) as (s & Hs & Hok). exists s. split; [| exact Hok].
  rewrite <- Hs. apply (KFR cid pos'); [exact HinSc|].
  right. unfold in_zr. cbn [fst snd].
  destruct (frame_al64 SEGS B lyc Sc W memc mdc cid pos' HARc HinSc) as (Hal64 & Hbal & Hb64).
  pose proof (Z.div_mod (frame_addr lyc cid pos') 64 ltac:(lia)) as D1. rewrite Hal64, Z.add_0_r in D1.
  pose proof (Z.div_mod (fs_frame_bytes cid) 64 ltac:(lia)) as D2. rewrite Hbal, Z.add_0_r in D2.
  assert (E1 : frame_addr lyc cid pos' / 8 = 8 * (frame_addr lyc cid pos' / 64)).
  { replace (frame_addr lyc cid pos') with (8 * (frame_addr lyc cid pos' / 64) * 8) at 1 by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  assert (E2 : fs_frame_bytes cid / 8 = 8 * (fs_frame_bytes cid / 64)).
  { replace (fs_frame_bytes cid) with (8 * (fs_frame_bytes cid / 64) * 8) at 1 by lia.
    rewrite Z.div_mul by lia. reflexivity. }
  destruct Hcase as [(Happ & Hzr) | (Hband & Hzr)].
  + unfold in_zr, frame_rng in Hzr. cbn [fst snd] in Hzr.
    pose proof (Z.div_mod x 8 ltac:(lia)) as Dx2. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Dxb2.
    unfold shadow_of_addr, shadow_addr. rewrite E1, E2.
    set (u := frame_addr lyc cid pos' / 64) in *. set (w := fs_frame_bytes cid / 64) in *.
    set (qx := x / 8) in *. set (xm := x mod 8) in *. clearbody u w qx xm.
    clear - D1 D2 Dx2 Dxb2 Hzr. lia.
  + exfalso. apply (cl_amem_out_band q nn x HAMR Hx).
    pose proof asan_consts as (_ & _ & _ & _ & Clm). unfold SHADOW_OFF. lia.
Qed.

(* What the copy-out segment needs of a range the caller may write, at a later state of the walk. *)
Lemma pd_tsrc_inner : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
  S2 mem3 md3 pos sp q nn,
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
  ajournal SEGS B STK sp0 FP ly S W0 mem0 md0 ((0, pos) :: own) lyc S2 W mem3 md3 k ->
  frames S2 = (0, pos) :: frames Sc ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - PUT_DEC_STK <= a < sp) ->
     apresent (w_H W) memc a -> apresent (w_H W) mem3 a) ->
  (forall cid pos' a, In (cid, pos') (frames Sc) ->
     (in_zr a (frame_rng lyc (cid, pos')) \/
      in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
     aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a) ->
  twr_ok B STK sp0 FP ly S lyc Sc own W memc sp q nn ->
  tsrc_ok W memc sp q nn ->
  (q + nn <= sp - PUT_DEC_STK \/ sp <= q) ->
  tsrc0_ok W mem3 (sp - 96) q nn.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem3 md3 pos sp q nn
HJc HJ3 Hfrs2 Eab HPG KFR HWR HSR Hside.
assert (Hes : ESTACK = 4096) by reflexivity. assert (HSTK : PUT_DEC_STK = 4208) by reflexivity.
pose proof (pd_twr_inner STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem3 md3 pos sp q nn
  HJc HJ3 Hfrs2 Eab HPG HWR Hside) as HWR3.
pose proof HSR as (HS1 & HRA & HHull & HAM & HQ0 & HQ1).
split.
- intros a Ha. split;
  [ apply (aview_some_of_apresent SEGS); exact (proj1 (proj2 (HWR3 a Ha))) | lia ].
- split; [| split; [exact HAM | split; [exact HQ0 | exact HQ1]]].
  intros x Hx.
  exact (pd_cell_at STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem3 md3 sp q nn x
    HJc (proj1 HJ3) Eab KFR HWR HSR Hx).
Qed.

(* A byte of the caller's picture -- a heap block, a frame zone, or the image -- is apart from the
   frame put_dec took, from its shadow and from its flag. *)
Lemma pd_sep_zone : forall lyc Sc S2 (W : world SEGS) mem2 md2 pos a,
  AR SEGS B lyc S2 W mem2 md2 ->
  ablocks B lyc S2 = ablocks B lyc Sc ->
  frames S2 = (0, pos) :: frames Sc ->
  ((exists bb m i, In (bb, m) (ablocks B lyc Sc) /\ 0 <= i < req_size m /\ a = bb + i) \/
   (exists cid pos', In (cid, pos') (frames Sc) /\
      (in_zr a (frame_rng lyc (cid, pos')) \/
       in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8))) \/
   in_img SEGS a) ->
  ~ (frame_addr lyc 0 pos <= a < frame_addr lyc 0 pos + 64) /\
  ~ (SB + frame_addr lyc 0 pos / 8 <= a < SB + frame_addr lyc 0 pos / 8 + 8) /\
  a <> flag_addr lyc 0 pos.
Proof.
intros lyc Sc S2 W mem2 md2 pos a HAR2 Eab Hfrs2 Hwhere.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
destruct (frames_bounds SEGS B LAWS lyc S2 W mem2 md2 0 pos HAR2 Hin2) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 0) with 64 in HFceil, HFapp.
assert (Hpos0 : 0 <= pos < fs_frames 0)
  by (destruct HAR2 as (M1 & _); exact (proj1 (proj2 (frame_facts B lyc S2 _ 0 pos M1 Hin2)))).
destruct (FFL lyc S2 W mem2 md2 0 pos HAR2 Hin2) as (HFLpres & HFLown & HFLapp & HFLceil).
pose proof (frm_off_imgP B lyc S2 W mem2 md2 0 pos HAR2 Hin2) as HFimg.
change (fs_frame_bytes 0) with 64 in HFimg.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc 0 pos) ltac:(lia)) as HSB1.
pose proof (YCbq.shadow_addr_bounds (frame_addr lyc 0 pos + 64) ltac:(lia)) as HSB2.
assert (HSBF : shadow_addr (frame_addr lyc 0 pos) = SB + frame_addr lyc 0 pos / 8)
  by (unfold shadow_addr, SB, SHADOW_OFF; lia).
pose proof (shadow_range_end (frame_addr lyc 0 pos) 64 ltac:(lia)) as Hre.
change (64 / 8) with 8 in Hre.
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp.
destruct Hwhere as [(bb & m & i & Hin & Hi & ->) | [(cid & pos' & Hin & Hcase) | Himg]].
- assert (Hinb : In (bb, m) (ablocks B lyc S2)) by (rewrite Eab; exact Hin).
  destruct (al_blocks _ _ LAWS lyc S2 W mem2 md2 bb m HAR2 Hinb) as (_ & H4096 & Hce & Happ2 & Hbp & _).
  pose proof (sep_block_frame SEGS B LAWS lyc S2 W mem2 md2 bb m 0 pos HAR2 Hinb Hin2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (fs_frame_bytes 0) with 64 in Hd.
  unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ2.
  split; [lia|].
  split; [rewrite <- HSBF; intros Hx; unfold kLowMemEnd, kHighShadowEnd in *; lia|].
  intros Heq. apply (proj2 (Hbp (bb + i) ltac:(lia))). rewrite Heq. exact HFLown.
- assert (HinS2 : In (cid, pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin).
  destruct (al_frames _ _ LAWS lyc S2 W mem2 md2 cid pos' HAR2 HinS2) as (_ & _ & Hfp & Hfs).
  assert (Hdj : (in_zr a (frame_rng lyc (0, pos)) \/
                 in_zr a (shadow_addr (frame_addr lyc 0 pos), fs_frame_bytes 0 / 8)) -> False).
  { intros Hr2. apply in_split in Hin as (l1 & l2 & El).
    apply (frames_zone_disj SEGS B LAWS lyc S2 W mem2 md2 (0, pos) (cid, pos') [] l1 l2 a HAR2);
    [rewrite Hfrs2, El; reflexivity | cbn [fst snd]; exact Hr2 | cbn [fst snd]; exact Hcase]. }
  split; [intros Hx; apply Hdj; left; unfold frame_rng, in_zr; cbn [fst snd];
          change (fs_frame_bytes 0) with 64; lia|].
  split; [intros Hx; apply Hdj; right; unfold in_zr; cbn [fst snd]; rewrite HSBF;
          change (fs_frame_bytes 0) with 64; change (64 / 8) with 8; lia|].
  destruct Hcase as [Hzr | Hzr].
  + unfold in_zr, frame_rng in Hzr. cbn [fst snd] in Hzr.
    intros Heq. apply (proj2 (Hfp a ltac:(lia))). rewrite Heq. exact HFLown.
  + unfold in_zr in Hzr. cbn [fst snd] in Hzr.
    intros Heq. apply (proj2 (Hfs (a - shadow_addr (frame_addr lyc cid pos')) ltac:(lia))).
    replace (shadow_addr (frame_addr lyc cid pos') + (a - shadow_addr (frame_addr lyc cid pos')))
      with a by lia. rewrite Heq. exact HFLown.
- pose proof (pa_img_range a Himg) as Hr. pose proof (pa_segs_low a Himg) as Hlow.
  split; [lia|]. split; [unfold kLowMemEnd in *; lia|].
  intros Heq.
  pose proof (pd_flag_off_img lyc S2 W mem2 md2 0 pos HAR2 ltac:(lia) Hpos0) as HFLimg.
  apply HFLimg. rewrite <- Heq. exact Himg.
Qed.

Ltac pd_inl := cbv [DL_KEPT PL_KEPT PD_CL_KEPT PD_CLB_KEPT]; cbn [In];
repeat (first [solve [left; reflexivity] | right]).

Theorem pb_put_dec : tput_dec_spec.
Proof.
unfold tput_dec_spec.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs b p n v mn
HJc Hra0 Hra4 Hgp Htp G10 G11 EV HV G13 Hmn Hal32 Hwlo Hwhi Hfrlen Hp8 Hb0 Hn0
HVP HWRp HWRb HSRp HSRb Hdisj Hpside Hbside Hev.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSTK : PUT_DEC_STK = 4208) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
pose proof (proj1 HJc) as HARc.
pose proof HJc as (_ & _ & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpresc & HST & _).
destruct HST as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
(* the digits of v, and how many of them *)
assert (Hv32 : 0 <= v < 2 ^ 32) by (rewrite <- EV; apply Z.mod_pos_bound; lia).
assert (Hnd1 : 1 <= Z.of_nat (length (put_dec.ds_lsb 10 v)))
  by (cbn [put_dec.ds_lsb length]; lia).
assert (Hnd10 : Z.of_nat (length (put_dec.ds_lsb 10 v)) <= 10)
  by (pose proof (put_dec.ds_lsb_length 10 v); lia).
assert (HDL : dec_len v mn = Z.max mn (Z.of_nat (length (put_dec.ds_lsb 10 v)))).
{ unfold put_dec_c.dec_len, DEC. rewrite length_app, repeat_length.
  rewrite put_dec.dec_ds by lia. rewrite length_rev. lia. }
assert (HK1 : 1 <= dec_len v mn <= 10) by (rewrite HDL; lia).
(* the prologue *)
eapply SRr_bind.
{ exact (pd_entry STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p b mn
    HJc Hra0 Hra4 Hgp Htp G10 G11 G13 Hmn Hal32 Hwlo Hwhi Hfrlen). }
cbv beta.
intros W1 c1 _ (-> & S2 & pos & regs1 & mem1 & md1 & -> & HJ1 & Hfrs2 & Eab & Hnev & Hbb &
  P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 &
  P18 & P19 & P20 & P21 & P22 & P23 & P24 & P25 & P26 & P27 & P28 & P29 &
  V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & HFLG & (junk & Hjlen & HGJ) & HRA1 & HPG1 & HPW1 &
  KA1 & KB1 & KC1 & KD1).
assert (Hin2 : In (0, pos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
set (F := frame_addr lyc 0 pos) in *.
destruct (frames_bounds SEGS B LAWS lyc S2 W mem1 md1 0 pos (proj1 HJ1) Hin2) as (HF4096 & HFceil & HFapp).
change (fs_frame_bytes 0) with 64 in HFceil, HFapp.
destruct (FFL lyc S2 W mem1 md1 0 pos (proj1 HJ1) Hin2) as (_ & _ & HFLapp & HFLceil).
unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFLapp.
pose proof (YCbq.shadow_addr_bounds F ltac:(clear - HF4096 HFceil C1 C4; lia)) as HSB1.
pose proof (YCbq.shadow_addr_bounds (F + 64) ltac:(clear - HF4096 HFceil C1 C4; lia)) as HSB2.
assert (HSBF : shadow_addr F = SB + F / 8) by (unfold shadow_addr, SB, SHADOW_OFF; lia).
pose proof (shadow_range_end F 64 ltac:(lia)) as Hre. change (64 / 8) with 8 in Hre.
assert (Hpos0 : 0 <= pos < fs_frames 0).
{ destruct (proj1 HJ1) as (M1 & _). exact (proj1 (proj2 (frame_facts B lyc S2 _ 0 pos M1 Hin2))). }
(* every byte of the caller's two ranges is apart from the new frame, its shadow and its flag *)
assert (SEPp : forall a, p <= a < p + 8 ->
  ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\
  a <> flag_addr lyc 0 pos /\ ~ in_img SEGS a).
{ intros a Ha. apply (pd_caller_sep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem1 md1 pos a
    HJc (proj1 HJ1) Eab Hfrs2 Hpos0
    (proj1 (HWRp a Ha))). }
assert (SEPb : forall a, b + n <= a < b + n + dec_len v mn ->
  ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\
  a <> flag_addr lyc 0 pos /\ ~ in_img SEGS a).
{ intros a Ha. apply (pd_caller_sep STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem1 md1 pos a
    HJc (proj1 HJ1) Eab Hfrs2 Hpos0
    (proj1 (HWRb a Ha))). }
(* the digit loop *)
eapply SRr_bind.
{ eapply (pd_dloop 10%nat STK sp0 FP ly S W0 mem0 md0 own lyc S2 W mem1 md1 k regs1 pos
    (F + 32) 0 v (getr regs 12) [] junk).
  - lia.
  - change (10 ^ Z.of_nat 10) with 10000000000. lia.
  - exact EV.
  - exact HV.
  - exact HJ1.
  - exact Hin2.
  - reflexivity.
  - reflexivity.
  - rewrite Hjlen. lia.
  - cbn [length]. lia.
  - cbn [app]. exact HGJ.
  - exact HRA1.
  - rewrite Z.add_0_r. exact P5.
  - exact P6.
  - exact P7.
  - rewrite Z.add_0_r. exact P11.
  - exact P16.
  - exact P17.
  - exact P21.
  - exact P22.
  - exact P28. }
cbv beta.
intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HG2 & KD2 & HPG2 & HRA2 &
  Q5 & Q11 & Q16 & Q17 & Q21 & Q6 & Q7 & Q28 & QK).
(* the junk bytes of the digit buffer, as a byte list *)
assert (Hjbnd : forall j, (j < length junk)%nat -> 0 <= nth j junk 0 < 256)
  by (intros j Hj; exact (proj2 (HGJ j Hj))).
pose proof (pd_map_unsig junk Hjbnd) as HjB.
assert (HjBlen : length (map (Z_to_bv 8) junk) = 10%nat) by (rewrite length_map; exact Hjlen).
(* the zero padding *)
eapply SRr_bind.
{ rewrite Z.add_0_r in Q5, Q11. rewrite Z.add_0_l in Q16, Q17.
  eapply (pb_pd_pad W regs2 mem2 md2 STK sp0 FP ly S W0 mem0 md0 own lyc S2 pos k
    (Z.of_nat (length (put_dec.ds_lsb 10 v))) mn (put_dec.ds_lsb 10 v)
    (skipn (length (put_dec.ds_lsb 10 v)) (map (Z_to_bv 8) junk))).
  - exact HJ2.
  - lia.
  - exact Hmn.
  - reflexivity.
  - rewrite length_skipn, HjBlen. lia.
  - exact Q5.
  - exact Q11.
  - exact Q16.
  - exact Q17.
  - rewrite (QK 20%bv ltac:(pd_inl)). exact P20.
  - rewrite (QK 22%bv ltac:(pd_inl)). exact P22.
  - rewrite map_app, pd_skipn_map, HjB. cbn [app] in HG2. exact HG2.
  - exact HRA2. }
cbv beta.
intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & PK3 & T16 & T5 & T11 & HG3 & HRA3 & KP).
(* the copy-out: the digits, then the counter *)
assert (HLlen : length (put_dec.ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat (mn - Z.of_nat (length (put_dec.ds_lsb 10 v))))
   ++ skipn (Z.to_nat (mn - Z.of_nat (length (put_dec.ds_lsb 10 v))))
        (skipn (length (put_dec.ds_lsb 10 v)) (map (Z_to_bv 8) junk))) = 10%nat).
{ rewrite !length_app, repeat_length, !length_skipn, HjBlen. lia. }
assert (HKn : Z.to_nat (dec_len v mn) =
  length (put_dec.ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat (mn - Z.of_nat (length (put_dec.ds_lsb 10 v)))))).
{ rewrite length_app, repeat_length, HDL.
  destruct (Z.le_ge_cases mn (Z.of_nat (length (put_dec.ds_lsb 10 v)))) as [Hle | Hge];
  [rewrite Z.max_r by lia | rewrite Z.max_l by lia]; lia. }
assert (HprLen : Z.of_nat (length (firstn (Z.to_nat (dec_len v mn))
  (map bv_unsigned (put_dec.ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat (mn - Z.of_nat (length (put_dec.ds_lsb 10 v))))
   ++ skipn (Z.to_nat (mn - Z.of_nat (length (put_dec.ds_lsb 10 v))))
        (skipn (length (put_dec.ds_lsb 10 v)) (map (Z_to_bv 8) junk)))))) = dec_len v mn).
{ rewrite length_firstn, length_map, HLlen.
  rewrite Nat.min_l by lia. lia. }
assert (R2 : getr regs3 2 = Z_to_bv 64 (spZ regs - 96))
  by (rewrite (PK3 2%bv ltac:(pd_inl)), (QK 2%bv ltac:(pd_inl)); exact P2).
assert (Hsp3 : spZ regs3 = spZ regs - 96)
  by (unfold spZ at 1; rewrite R2; apply unsigned_lit_small; lia).
assert (R14 : getr regs3 14 = w64 (F + 32))
  by (rewrite (PK3 14%bv ltac:(pd_inl)), (QK 14%bv ltac:(pd_inl)); exact P14).
assert (R15 : getr regs3 15 = w64 (Z.lxor (F + 32) 18446744073709551615)).
{ rewrite (PK3 15%bv ltac:(pd_inl)), (QK 15%bv ltac:(pd_inl)), P15. apply pd_not_word. lia. }
assert (R18 : getr regs3 18 = w64 p)
  by (rewrite (PK3 18%bv ltac:(pd_inl)), (QK 18%bv ltac:(pd_inl)); exact P18).
assert (R19 : getr regs3 19 = w64 b)
  by (rewrite (PK3 19%bv ltac:(pd_inl)), (QK 19%bv ltac:(pd_inl)); exact P19).
assert (R22 : getr regs3 22 = w64 SB)
  by (rewrite (PK3 22%bv ltac:(pd_inl)), (QK 22%bv ltac:(pd_inl)); exact P22).
assert (KEEP13 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 42) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem1 a).
{ intros a Ha Hn. rewrite (KP a Ha Hn). apply KD2; [exact Ha | lia]. }
assert (KFR3x : forall cid pos' a, In (cid, pos') (frames Sc) ->
  (in_zr a (frame_rng lyc (cid, pos')) \/
   in_zr a (shadow_addr (frame_addr lyc cid pos'), fs_frame_bytes cid / 8)) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a).
{ intros cid pos' a Hin Hr.
  assert (HinS2 : In (cid, pos') (frames S2)) by (rewrite Hfrs2; right; exact Hin).
  destruct (frame_zone SEGS B LAWS lyc S2 W mem1 md1 cid pos' a (proj1 HJ1) HinS2 Hr) as (Hceil' & Hcase).
  assert (Haz : 0 <= a < 2 ^ 64).
  { destruct Hcase as [(Hr1 & Happ') | Hr2];
    [ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ'; lia
    | unfold kLowMemEnd, kHighShadowEnd in Hr2; lia ]. }
  rewrite (KEEP13 a Haz).
  - exact (KD1 cid pos' a Hin Hr).
  - apply in_split in Hin as (l1 & l2 & El).
    intros Hx. apply (frames_zone_disj SEGS B LAWS lyc S2 W mem1 md1 (0, pos) (cid, pos') [] l1 l2 a (proj1 HJ1));
    [ rewrite Hfrs2, El; reflexivity
    | cbn [fst snd]; left; unfold frame_rng, in_zr; cbn [fst snd]; change (fs_frame_bytes 0) with 64; lia
    | cbn [fst snd]; exact Hr ]. }
assert (HPG13 : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - PUT_DEC_STK <= a < spZ regs) ->
  apresent (w_H W) memc a -> apresent (w_H W) mem3 a).
{ intros a Ha Hw Hp. apply (pd_pres_of_view W mem2 mem3 a ltac:(lia)
    ltac:(intros Hi; pose proof (pa_segs_low a Hi); unfold kLowMemEnd in *; lia)
    ltac:(apply KP; [lia | lia])).
  apply HPG2. apply HPG1; [exact Ha | exact Hw | exact Hp]. }
set (LL := put_dec.ds_lsb 10 v ++ repeat (dg 0) (Z.to_nat (mn - Z.of_nat (length (put_dec.ds_lsb 10 v))))
   ++ skipn (Z.to_nat (mn - Z.of_nat (length (put_dec.ds_lsb 10 v))))
        (skipn (length (put_dec.ds_lsb 10 v)) (map (Z_to_bv 8) junk))) in *.
assert (SEPab : forall a, (p <= a < p + 8 \/ b + n <= a < b + n + dec_len v mn) ->
  ~ (F <= a < F + 64) /\ ~ (SB + F / 8 <= a < SB + F / 8 + 8) /\
  a <> flag_addr lyc 0 pos /\ ~ in_img SEGS a)
  by (intros a [Ha | Ha]; [exact (SEPp a Ha) | exact (SEPb a Ha)]).
pose proof HSRp as (_ & _ & _ & _ & HPlo & HPhi).
pose proof HSRb as (_ & _ & _ & _ & HBlo & HBhi).
assert (HdjPD : p + 8 <= F + 32 \/ F + 32 + dec_len v mn <= p).
{ destruct (Z_le_gt_dec (p + 8) (F + 32)) as [HH|H1]; [left; exact HH|].
  destruct (Z_le_gt_dec (F + 32 + dec_len v mn) p) as [HH|H2]; [right; exact HH|].
  exfalso. destruct (SEPab (Z.max p (F + 32)) ltac:(left; lia)) as (Hnf & _). apply Hnf. lia. }
assert (HdjBD : b + n + dec_len v mn <= F + 32 \/ F + 32 + dec_len v mn <= b + n).
{ destruct (Z_le_gt_dec (b + n + dec_len v mn) (F + 32)) as [HH|H1]; [left; exact HH|].
  destruct (Z_le_gt_dec (F + 32 + dec_len v mn) (b + n)) as [HH|H2]; [right; exact HH|].
  exfalso. destruct (SEPab (Z.max (b + n) (F + 32)) ltac:(right; lia)) as (Hnf & _). apply Hnf. lia. }
assert (KEEPc : forall a, (p <= a < p + 8 \/ b + n <= a < b + n + dec_len v mn) ->
  aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) memc a).
{ intros a Ha. destruct (SEPab a Ha) as (Hf & Hs & Hfl & Hni).
  assert (HW : awr_byte STK sp0 FP (ablocks B ly S) (ablocks B lyc Sc) lyc own a)
    by (destruct Ha; [exact (proj1 (HWRp a ltac:(lia))) | exact (proj1 (HWRb a ltac:(lia)))]).
  assert (Haz : 0 <= a < 2 ^ 64) by (clear - Ha HPlo HPhi HBlo HBhi HK1; lia).
  rewrite (KEEP13 a Haz ltac:(clear - Hf; lia)).
  destruct (awr_byte_cases SEGS B LAWS STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k a HJc HW)
    as (_ & [[Hc Hst] | [(Happ & b0 & m0 & Hin & Hr & _) | (cid & pos' & Hin & Hcase)]]).
  - apply KA1; [clear - Hc Haz; lia | clear - Ha Hpside Hbside HK1; lia].
  - replace a with (b0 + (a - b0)) by (clear - Hr; lia).
    apply (KB1 b0 m0 (a - b0)); [exact Hin | clear - Hr; lia].
  - apply (KD1 cid pos' a ltac:(rewrite Hfrs; apply in_or_app; left; exact Hin)).
    destruct Hcase as [(_ & Hz) | (_ & Hz)]; [left; exact Hz | right; exact Hz]. }
(* the copy-out *)
eapply SRr_bind.
{ eapply (pd_copy_seg (firstn (Z.to_nat (dec_len v mn)) (map bv_unsigned LL))
    W regs3 mem3 md3 STK sp0 k FP ly S W0 mem0 md0 own pos lyc S2 p b n (F + 32) (dec_len v mn)).
  - exact HprLen.
  - exact HK1.
  - exact HJ3.
  - exact Hin2.
  - reflexivity.
  - exact Hb0.
  - exact Hn0.
  - exact Hp8.
  - exact R14.
  - exact R15.
  - rewrite T16, HDL. f_equal. lia.
  - exact R18.
  - exact R19.
  - exact R22.
  - rewrite Hsp3. apply (pd_twr_inner STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem3 md3
      pos (spZ regs) p 8 HJc HJ3 Hfrs2 Eab HPG13 HWRp ltac:(clear - Hpside; lia)).
  - rewrite Hsp3. apply (pd_twr_inner STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem3 md3
      pos (spZ regs) (b + n) (dec_len v mn) HJc HJ3 Hfrs2 Eab HPG13 HWRb ltac:(clear - Hbside; lia)).
  - rewrite Hsp3. apply (pd_tsrc_inner STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem3 md3
      pos (spZ regs) p 8 HJc HJ3 Hfrs2 Eab HPG13 KFR3x HWRp HSRp ltac:(clear - Hpside; lia)).
  - rewrite Hsp3. apply (pd_tsrc_inner STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k S2 mem3 md3
      pos (spZ regs) (b + n) (dec_len v mn) HJc HJ3 Hfrs2 Eab HPG13 KFR3x HWRb HSRb ltac:(clear - Hbside; lia)).
  - apply (range_addressable_sub _ _ (F + 32) 10); [exact HRA3 | lia | lia].
  - exact Hdisj.
  - exact HdjPD.
  - exact HdjBD.
  - apply (val_mem_kept SEGS (w_H W) (w_H W) memc mem3);
    [intros kk Hk; apply KEEPc; left; lia | exact HVP].
  - apply pd_garr8_firstn. exact HG3. }
cbv beta.
intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HJ4 & CK & HGB & HVP4 & HGD4 & KC & HPG4).
assert (KEEP14 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 32 <= a < F + 42) ->
  ~ (p <= a < p + 8) -> ~ (b + n <= a < b + n + dec_len v mn) ->
  aview SEGS (w_H W) mem4 a = aview SEGS (w_H W) mem1 a).
{ intros a Ha H1 H2 H3. rewrite (KC a Ha H2 H3). apply KEEP13; [exact Ha | exact H1]. }
assert (HnotP : forall a, F <= a < F + 64 -> ~ (p <= a < p + 8)).
{ intros a Ha Hx. destruct (SEPab a ltac:(left; lia)) as (Hnf & _). apply Hnf. lia. }
assert (HnotB : forall a, F <= a < F + 64 -> ~ (b + n <= a < b + n + dec_len v mn)).
{ intros a Ha Hx. destruct (SEPab a ltac:(right; lia)) as (Hnf & _). apply Hnf. lia. }
(* the frame release and the epilogue *)
eapply SRr_bind.
{ eapply (pd_tail STK sp0 FP ly S W0 mem0 md0 own lyc S2 W mem4 md4 k regs4 regs pos).
  - exact HJ4.
  - exact Hra0.
  - rewrite (CK 3%bv ltac:(pd_inl)), (PK3 3%bv ltac:(pd_inl)), (QK 3%bv ltac:(pd_inl)), P3.
    symmetry. exact Hgp.
  - rewrite (CK 4%bv ltac:(pd_inl)), (PK3 4%bv ltac:(pd_inl)), (QK 4%bv ltac:(pd_inl)), P4.
    symmetry. exact Htp.
  - rewrite (CK 8%bv ltac:(pd_inl)), (PK3 8%bv ltac:(pd_inl)), (QK 8%bv ltac:(pd_inl)). exact P8.
  - rewrite (CK 10%bv ltac:(pd_inl)), (PK3 10%bv ltac:(pd_inl)), (QK 10%bv ltac:(pd_inl)). exact P10.
  - rewrite (CK 12%bv ltac:(pd_inl)), (PK3 12%bv ltac:(pd_inl)), (QK 12%bv ltac:(pd_inl)). exact P12.
  - rewrite (CK 13%bv ltac:(pd_inl)), (PK3 13%bv ltac:(pd_inl)), (QK 13%bv ltac:(pd_inl)). exact P13.
  - rewrite (CK 23%bv ltac:(pd_inl)), (PK3 23%bv ltac:(pd_inl)), (QK 23%bv ltac:(pd_inl)). exact P23.
  - rewrite (CK 24%bv ltac:(pd_inl)), (PK3 24%bv ltac:(pd_inl)), (QK 24%bv ltac:(pd_inl)). exact P24.
  - rewrite (CK 25%bv ltac:(pd_inl)), (PK3 25%bv ltac:(pd_inl)), (QK 25%bv ltac:(pd_inl)). exact P25.
  - rewrite (CK 26%bv ltac:(pd_inl)), (PK3 26%bv ltac:(pd_inl)), (QK 26%bv ltac:(pd_inl)). exact P26.
  - rewrite (CK 27%bv ltac:(pd_inl)), (PK3 27%bv ltac:(pd_inl)), (QK 27%bv ltac:(pd_inl)). exact P27.
  - apply rdword_of_val_mem; [| clear - HFLapp HFLceil C1; lia].
    apply (val_mem_kept SEGS (w_H W) (w_H W) mem1 mem4);
    [ intros kk Hk; apply KEEP14;
      [ clear - Hk HF4096 HFceil C1; lia | clear - Hk; lia
      | apply HnotP; clear - Hk; lia | apply HnotB; clear - Hk; lia ]
    | exact (val_mem_of_rdword SEGS (w_H W) mem1 _ _ HFLG) ].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem1 mem4);
    [intros kk Hk; apply KEEP14;
     [ clear - Hk Hwlo Hwhi Hceil Hslo Hshi H47 HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hwlo Hceil Hslo HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hpside HSTK Hes; lia | clear - Hk Hbside HSTK Hes HK1; lia ] | exact V1].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem1 mem4);
    [intros kk Hk; apply KEEP14;
     [ clear - Hk Hwlo Hwhi Hceil Hslo Hshi H47 HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hwlo Hceil Hslo HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hpside HSTK Hes; lia | clear - Hk Hbside HSTK Hes HK1; lia ] | exact V2].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem1 mem4);
    [intros kk Hk; apply KEEP14;
     [ clear - Hk Hwlo Hwhi Hceil Hslo Hshi H47 HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hwlo Hceil Hslo HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hpside HSTK Hes; lia | clear - Hk Hbside HSTK Hes HK1; lia ] | exact V3].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem1 mem4);
    [intros kk Hk; apply KEEP14;
     [ clear - Hk Hwlo Hwhi Hceil Hslo Hshi H47 HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hwlo Hceil Hslo HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hpside HSTK Hes; lia | clear - Hk Hbside HSTK Hes HK1; lia ] | exact V4].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem1 mem4);
    [intros kk Hk; apply KEEP14;
     [ clear - Hk Hwlo Hwhi Hceil Hslo Hshi H47 HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hwlo Hceil Hslo HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hpside HSTK Hes; lia | clear - Hk Hbside HSTK Hes HK1; lia ] | exact V5].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem1 mem4);
    [intros kk Hk; apply KEEP14;
     [ clear - Hk Hwlo Hwhi Hceil Hslo Hshi H47 HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hwlo Hceil Hslo HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hpside HSTK Hes; lia | clear - Hk Hbside HSTK Hes HK1; lia ] | exact V6].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem1 mem4);
    [intros kk Hk; apply KEEP14;
     [ clear - Hk Hwlo Hwhi Hceil Hslo Hshi H47 HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hwlo Hceil Hslo HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hpside HSTK Hes; lia | clear - Hk Hbside HSTK Hes HK1; lia ] | exact V7].
  - apply (val_mem_kept SEGS (w_H W) (w_H W) mem1 mem4);
    [intros kk Hk; apply KEEP14;
     [ clear - Hk Hwlo Hwhi Hceil Hslo Hshi H47 HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hwlo Hceil Hslo HSTK Hes HFceil HF4096 C1; lia
     | clear - Hk Hpside HSTK Hes; lia | clear - Hk Hbside HSTK Hes HK1; lia ] | exact V8].
  - lia. }
cbv beta.
intros W5 c5 _ (-> & regs5 & mem5 & md5 & -> & HJ5 & HAREG & HFRS5 & HABL5 & KT & HPG5).
(* the post of the contract *)
apply SRr_ret. unfold tput_dec_post.
exists lyc, (stack_free_state 0 pos S2), regs5, mem5, md5.
split; [reflexivity|].
split; [unfold EV_PUT_DEC; rewrite Z.add_0_r; exact HJ5|].
split; [exact HAREG|].
split; [rewrite Hfrs2 in HFRS5; injection HFRS5 as HF5; symmetry; exact HF5|].
split; [rewrite HABL5; exact Eab|].
split.
{ split.
  { intros a Ha Hw HnE.
    rewrite (KT a ltac:(clear - Ha C1; lia)
      ltac:(fold F; clear - Ha HFceil C1; lia)
      ltac:(fold F; clear - Ha HSB1 HSB2 Hre HSBF C1 C2 C5; lia)
      ltac:(clear - Ha HFLceil C1; lia)).
    rewrite (KC a ltac:(clear - Ha C1; lia) ltac:(clear - HnE; tauto) ltac:(clear - HnE; tauto)).
    rewrite (KEEP13 a ltac:(clear - Ha C1; lia) ltac:(fold F; clear - Ha HFceil C1; lia)).
    apply KA1; [exact Ha | exact Hw]. }
  split.
  { intros bb m i Hin Hi HnE.
    destruct (pd_sep_zone lyc Sc S2 W mem1 md1 pos (bb + i) (proj1 HJ1) Eab Hfrs2
      ltac:(left; exists bb, m, i; split; [exact Hin | split; [exact Hi | reflexivity]])) as (Hf & Hs & Hfl).
    destruct (al_blocks _ _ LAWS lyc Sc W memc mdc bb m HARc Hin) as (_ & H4096b & Hceb & _ & _ & _).
    assert (Hab : 0 <= bb + i < 2 ^ 64) by (clear - H4096b Hceb Hi C1; lia).
    rewrite (KT (bb + i) Hab Hf Hs Hfl).
    rewrite (KC (bb + i) Hab ltac:(clear - HnE; tauto) ltac:(clear - HnE; tauto)).
    rewrite (KEEP13 (bb + i) Hab ltac:(clear - Hf; lia)).
    apply (KB1 bb m i); [exact Hin | exact Hi]. }
  split.
  { intros a Hi Hns He.
    destruct (pd_sep_zone lyc Sc S2 W mem1 md1 pos a (proj1 HJ1) Eab Hfrs2
      ltac:(right; right; exact Hi)) as (Hf & Hs & Hfl).
    pose proof (pa_segs_low a Hi) as Hlow.
    assert (Hab : 0 <= a < 2 ^ 64) by (clear - Hlow C5; unfold kLowMemEnd in *; lia).
    rewrite (KT a Hab Hf Hs Hfl).
    rewrite (KC a Hab
      ltac:(intros Hx; destruct (SEPab a ltac:(left; exact Hx)) as (_ & _ & _ & Hni); exact (Hni Hi))
      ltac:(intros Hx; destruct (SEPab a ltac:(right; exact Hx)) as (_ & _ & _ & Hni); exact (Hni Hi))).
    rewrite (KEEP13 a Hab ltac:(clear - Hf; lia)).
    apply KC1; [exact Hi | exact Hns | exact He]. }
  split.
  { intros cid pos' a Hin Hr HnE.
    destruct (pd_sep_zone lyc Sc S2 W mem1 md1 pos a (proj1 HJ1) Eab Hfrs2
      ltac:(right; left; exists cid, pos'; split; [exact Hin | exact Hr])) as (Hf & Hs & Hfl).
    destruct (frame_zone SEGS B LAWS lyc Sc W memc mdc cid pos' a HARc Hin Hr) as (Hceil' & Hcase).
    assert (Hab : 0 <= a < 2 ^ 64).
    { destruct Hcase as [(Hr1 & Happ') | Hr2];
      [ unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in Happ';
        clear - Happ' Hr1 Hceil' C1; lia
      | clear - Hr2 C2 C5; unfold kLowMemEnd, kHighShadowEnd in *; lia ]. }
    rewrite (KT a Hab Hf Hs Hfl).
    rewrite (KC a Hab ltac:(clear - HnE; tauto) ltac:(clear - HnE; tauto)).
    rewrite (KEEP13 a Hab ltac:(clear - Hf; lia)).
    apply (KD1 cid pos' a Hin Hr). }
  split.
  { intros a Ha Hw Hp. apply HPG5. apply HPG4. apply HPG13; [exact Ha | exact Hw | exact Hp]. }
  { intros a Ha. apply HPG5. apply HPG4.
    apply (pd_pres_of_view W mem1 mem3 a
      ltac:(clear - Ha Hwlo Hwhi Hceil Hslo Hshi H47 HSTK Hes C1; lia)
      ltac:(intros Hi; pose proof (pa_segs_low a Hi) as Hlw;
            clear - Ha Hlw Hwlo Hceil Hslo HSTK Hes C1 C5; unfold kLowMemEnd in *; lia)
      ltac:(apply KEEP13;
            [ clear - Ha Hwlo Hwhi Hceil Hslo Hshi H47 HSTK Hes C1; lia
            | clear - Ha Hwlo Hceil Hslo HSTK Hes HFceil HF4096 C1; lia ])).
    apply HPW1. exact Ha. } }
(* the digits at b + n, and the counter at p *)
assert (HDEC : rev (firstn (Z.to_nat (dec_len v mn)) LL) = DEC v mn).
{ unfold LL. rewrite app_assoc, HKn, pd_firstn_app_exact, rev_app_distr, pd_rev_repeat.
  unfold DEC. rewrite put_dec.dec_ds by lia. rewrite length_rev. f_equal. f_equal. lia. }
assert (HREV : rev (firstn (Z.to_nat (dec_len v mn)) (map bv_unsigned LL)) = map bv_unsigned (DEC v mn))
  by (rewrite <- pd_firstn_map, <- map_rev, HDEC; reflexivity).
rewrite HREV in HGB.
assert (HDLen : length (DEC v mn) = Z.to_nat (dec_len v mn))
  by (unfold put_dec_c.dec_len; lia).
split.
{ apply (pd_garr8_kept W mem4 mem5 (b + n) (map bv_unsigned (DEC v mn))); [| exact HGB].
  intros kk Hk. rewrite length_map, HDLen in Hk.
  destruct (SEPab (b + n + kk) ltac:(right; clear - Hk HK1; lia)) as (Hf & Hs & Hfl & _).
  apply KT; [clear - Hk HK1 HBlo HBhi; lia | exact Hf | exact Hs | exact Hfl]. }
{ apply (val_mem_kept SEGS (w_H W) (w_H W) mem4 mem5); [| exact HVP4].
  intros kk Hk. cbn [Z.of_nat] in Hk.
  destruct (SEPab (p + kk) ltac:(left; clear - Hk; lia)) as (Hf & Hs & Hfl & _).
  apply KT; [clear - Hk HPlo HPhi; lia | exact Hf | exact Hs | exact Hfl]. }
Qed.

Print Assumptions pb_put_dec.

End e.
End d.
End b.