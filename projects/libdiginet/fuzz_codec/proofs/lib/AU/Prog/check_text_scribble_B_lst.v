(* The symbolic state at check_text_scribble's text loop head 0x83ed4 in image B (segment L of
   check_text_scribble_B_inv.v), built from the boundary's values:
   atom 33 = q + i (the text byte's address), atom 34 = x = q[i], atom 35 = F + 32 + o (want[o]'s address), atom
   36 = y = q[i + 1] (read only after a dot); s7 = SB (atom 32), a4 = 46, a5 = 8 pinned; the text region of 1 or 2
   bytes at atom 33, want[o] writable at atom 35 (when o < n); the aliases q + i = atom 33, q + i + 1 = atom 33 + 1,
   F + 32 + o = atom 35, so the engine's address arithmetic (add a0,s5,s10 / add a0,s5,a0 / add a0,s6,a1) lands on
   the regions; the shadow entries of the text bytes and of want[o]; the ranges that decide the UBSan checks of
   q + i + 1 (0x83efc), want + o (0x83f24, 0x83f4c) and q + i (0x83f80): a3 = ~q and a2 = ~(F + 32) are at least
   2 ^ 64 - 2 ^ 47, a1, s3 at most 8, s10 at most 2 ^ 47 - 4. *)
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw0 YCef YF0l YCej YCeh YCem YCep.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU Require Import AWalkFw1 AWalkFw2 YCfm.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.A.Prog Require Import CodecCJ CPgBase.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import CPgBaseU CPgWalkU.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.AU.Prog Require Import check_text_scribble_B_inv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Definition bsl_sr : list sv := sr_set (sr_set (sr_set sr_atoms 23%bv (SOff 32 0)) 14%bv (SLit 46)) 15%bv (SLit 8).
Definition bsl_txt (two : bool) : YP09.region :=
  YP09.mkRegion (Some 33%nat) 0 (if two then 2 else 1) 0 0
    (YP09.mkChunk 0 (CVal 1 (SOff 34 0)) :: (if two then [YP09.mkChunk 1 (CVal 1 (SOff 36 0))] else [])).
Definition bsl_want : YP09.region := YP09.mkRegion (Some 35%nat) 0 1 0 1 [].
Definition bsl_rs (two wnt : bool) : smem := bsl_txt two :: (if wnt then [bsl_want] else []).
Definition bsl_G (xlo xhi ylo yhi flo fhi : Z) : facts :=
  mkFacts [(32%nat, mkAF SB SB 0); (33%nat, mkAF 1 (2 ^ 47 - 2) 0); (34%nat, mkAF xlo xhi 0);
           (35%nat, mkAF flo fhi 0); (36%nat, mkAF ylo yhi 0);
           (11%nat, mkAF 0 8 0); (19%nat, mkAF 0 8 0); (26%nat, mkAF 0 (2 ^ 47 - 2) 0);
           (13%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0); (12%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0)] []
    [(SAlu ALU_ADD (SOff 21 0) (SOff 26 0), SOff 33 0); (SAlu ALU_ADD (SOff 21 0) (SOff 26 1), SOff 33 1);
     (SAlu ALU_ADD (SOff 22 0) (SOff 11 0), SOff 35 0)].
Definition bsl_SH (two wnt : bool) : list shent :=
  mkSHE 33 0 (if two then 2 else 1) :: (if wnt then [mkSHE 35 0 1] else []).
Definition bsl_xs (q i x F o y : Z) : list Z := [q + i; x; F + 32 + o; y].

Lemma bsl_den_add : forall E (a b : nat) va vb c, ew E a = Z_to_bv 64 va -> ew E b = Z_to_bv 64 vb ->
  0 <= va -> 0 <= vb -> va + vb + c < 2 ^ 64 -> 0 <= c ->
  sv_denot E (SAlu ALU_ADD (SOff a 0) (SOff b c)) = Z_to_bv 64 (va + vb + c).
Proof.
intros E a b va vb c Ha Hb H1 H2 H3 H4. rewrite denot_lit_U. f_equal.
assert (Ra : 0 <= va < 2 ^ 64) by lia. assert (Ra0 : 0 <= va + 0 < 2 ^ 64) by lia.
assert (Rb : 0 <= vb < 2 ^ 64) by lia. assert (Rbc : 0 <= vb + c < 2 ^ 64) by lia.
rewrite U_SAlu. cbn [zalu_raw]. rewrite (U_atom_off E a va 0 Ha Ra Ra0), (U_atom_off E b vb c Hb Rb Rbc).
rewrite Z.add_0_r, Z.add_assoc. apply zcanon_id. unfold M64. lia.
Qed.

Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma bsl_state : forall (regs2 : bvmap 5 word) (W2 : world tfibsegs) mem2 q i o n F x y (two wnt : bool) xlo xhi ylo yhi
  flo fhi,
  getr regs2 23 = w64 SB -> getr regs2 14 = w64 46 -> getr regs2 15 = w64 8 ->
  getr regs2 21 = w64 q -> getr regs2 26 = w64 i -> getr regs2 22 = w64 (F + 32) -> getr regs2 11 = w64 o ->
  getr regs2 19 = w64 n -> getr regs2 13 = w64 (bnot q) -> getr regs2 12 = w64 (bnot (F + 32)) ->
  1 <= q -> 0 <= i -> q + i + 1 <= 2 ^ 47 - 1 -> 0 <= o <= n -> n <= 8 ->
  4096 <= F -> F + 64 <= 2 ^ 47 -> flo <= F + 32 + o <= fhi ->
  xlo <= x <= xhi -> 0 <= x < 256 -> ylo <= y <= yhi -> 0 <= y < 256 ->
  val_mem tfibsegs (mrestrict (w_H W2) mem2) (q + i) 1 x ->
  (two = true -> val_mem tfibsegs (mrestrict (w_H W2) mem2) (q + i + 1) 1 y) ->
  range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (q + i) (if two then 2 else 1) ->
  amem_range (q + i) (if two then 2 else 1) ->
  (wnt = true -> o < n /\ range_addressable (aview tfibsegs (w_H W2) mem2) SHADOW_OFF (F + 32 + o) 1 /\
     amem_range (F + 32 + o) 1 /\ apresent (w_H W2) mem2 (F + 32 + o) /\
     (forall a, q + i <= a < q + i + (if two then 2 else 1) -> a <> F + 32 + o)) ->
  st_ok tfibsegs (Ereg regs2 (cw_extra (bsl_xs q i x F o y)))
    (mkSS PC_L bsl_sr (bsl_rs two wnt) None (bsl_G xlo xhi ylo yhi flo fhi))
    (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 PC_L) mem2 (seg_rom tfibsegs))) /\
  sh_ok tfibsegs CW_Bx (bsl_SH two wnt) (Ereg regs2 (cw_extra (bsl_xs q i x F o y))) (mrestrict (w_H W2) mem2).
Proof.
intros regs2 W2 mem2 q i o n F x y two wnt xlo xhi ylo yhi flo fhi R23 R14 R15 R21 R26 R22 R11 R19 R13 R12
  Hq Hi Hqi Ho Hn HF0 HF1 Hfw Hx Hx8 Hy Hy8 Vx Vy Hra Ham Hw.
set (E := Ereg regs2 (cw_extra (bsl_xs q i x F o y))).
assert (EE : forall nn (r : bv 5), Z.of_nat nn = bv_unsigned r -> ew E nn = getr regs2 r)
  by (intros nn r Hnn; subst E; apply ew_Ereg_nat; exact Hnn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; apply cw_ew_SB).
assert (E33 : ew E 33 = Z_to_bv 64 (q + i)) by (subst E; exact (cw_ew_x regs2 (bsl_xs q i x F o y) 0)).
assert (E34 : ew E 34 = Z_to_bv 64 x) by (subst E; exact (cw_ew_x regs2 (bsl_xs q i x F o y) 1)).
assert (E35 : ew E 35 = Z_to_bv 64 (F + 32 + o)) by (subst E; exact (cw_ew_x regs2 (bsl_xs q i x F o y) 2)).
assert (E36 : ew E 36 = Z_to_bv 64 y) by (subst E; exact (cw_ew_x regs2 (bsl_xs q i x F o y) 3)).
assert (E21 : ew E 21 = Z_to_bv 64 q) by (rewrite (EE 21%nat 21%bv eq_refl); exact R21).
assert (E26 : ew E 26 = Z_to_bv 64 i) by (rewrite (EE 26%nat 26%bv eq_refl); exact R26).
assert (E22 : ew E 22 = Z_to_bv 64 (F + 32)) by (rewrite (EE 22%nat 22%bv eq_refl); exact R22).
assert (E11 : ew E 11 = Z_to_bv 64 o) by (rewrite (EE 11%nat 11%bv eq_refl); exact R11).
assert (E19 : ew E 19 = Z_to_bv 64 n) by (rewrite (EE 19%nat 19%bv eq_refl); exact R19).
assert (E13 : ew E 13 = Z_to_bv 64 (bnot q)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
assert (E12 : ew E 12 = Z_to_bv 64 (bnot (F + 32))) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (U32 : bv_unsigned (ew E 32) = SB) by (rewrite E32; apply unsigned_lit_small; unfold SB; lia).
assert (U33 : bv_unsigned (ew E 33) = q + i) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = x) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = F + 32 + o) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = y) by (rewrite E36; apply unsigned_lit_small; lia).
assert (U11 : bv_unsigned (ew E 11) = o) by (rewrite E11; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = n) by (rewrite E19; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = i) by (rewrite E26; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = bnot q) by (rewrite E13; apply unsigned_lit_small; unfold bnot; lia).
assert (U12 : bv_unsigned (ew E 12) = bnot (F + 32)) by (rewrite E12; apply unsigned_lit_small; unfold bnot; lia).
assert (Hk : 0 < (if two then 2 else 1) <= 2) by (destruct two; lia).
split.
- rewrite restrict_mkst_fx. apply (entry_st_ok_full tfibsegs); change (Ereg regs2 (cw_extra (bsl_xs q i x F o y))) with E.
  + unfold bsl_sr.
    apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Ereg | intros Hx0; discriminate Hx0 |] |
      intros Hx0; discriminate Hx0 |] | intros Hx0; discriminate Hx0 |].
    all: first [ rewrite R23; cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
               | rewrite R14; reflexivity | rewrite R15; reflexivity ].
  + destruct two, wnt; vm_compute; reflexivity.
  + unfold bsl_rs. apply Forall_cons.
    * unfold region_ok, bsl_txt. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U33. split; [lia|]. split; [destruct two; lia|]. split; [intros oo Hoo; lia|].
      apply Forall_cons.
      { apply (chunk_ok_val tfibsegs E _ (q + i) 0 1 (SOff 34 0) x); [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Vx. }
      destruct two; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val tfibsegs E _ (q + i) 1 1 (SOff 36 0) y); [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
      exact (Vy eq_refl).
    * destruct wnt; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
      destruct (Hw eq_refl) as (Ho' & _ & _ & Hpr & _).
      unfold region_ok, bsl_want. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U35. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros oo Hoo. apply (apresent_writable tfibsegs). replace (F + 32 + o + oo) with (F + 32 + o) by lia. exact Hpr.
  + destruct wnt.
    * destruct (Hw eq_refl) as (_ & _ & _ & _ & Hdj).
      assert (Hd : F + 32 + o + 1 <= q + i \/ q + i + (if two then 2 else 1) <= F + 32 + o).
      { destruct (Z_lt_le_dec (F + 32 + o) (q + i)); [left; lia|].
        destruct (Z_lt_le_dec (F + 32 + o) (q + i + (if two then 2 else 1))) as [Hlt|Hge]; [|right; lia].
        exfalso. exact (Hdj (F + 32 + o) ltac:(lia) eq_refl). }
      apply pairwise_disjoint_of_extents. unfold bsl_rs, bsl_txt, bsl_want, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U33, U35.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      destruct two; cbn in Hd; repeat split; lia.
    * apply pairwise_disjoint_of_extents. unfold bsl_rs, bsl_txt, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. cbn [zpairwise_disjoint zall_disjoint].
      repeat split.
  + split; [|split; [exact I|]].
    * unfold bsl_G. cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite U32, U33, U34, U35, U36, U11, U19, U26, U13, U12. rewrite Z.pow_0_r, !Z.mod_1_r.
      unfold bnot, SB. repeat (split; [repeat split; lia|]). exact I.
    * unfold bsl_G. cbn [f_alias alias_ok].
      split; [rewrite (bsl_den_add E 21 26 q i 0 E21 E26 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)), Z.add_0_r;
              cbn [sv_denot]; rewrite U33, Z.add_0_r; reflexivity|].
      split; [rewrite (bsl_den_add E 21 26 q i 1 E21 E26 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia));
              cbn [sv_denot]; rewrite U33; f_equal; lia|].
      split; [|exact I].
      rewrite (bsl_den_add E 22 11 (F + 32) o 0 E22 E11 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)), Z.add_0_r.
      cbn [sv_denot]. rewrite U35, Z.add_0_r. reflexivity.
- unfold bsl_SH. apply Forall_cons.
  + apply (cw_shent_ra W2 mem2 E 33 (q + i) (if two then 2 else 1) Hra Ham ltac:(lia) ltac:(destruct two; lia)
      ltac:(destruct two; lia) E33 E32).
  + destruct wnt; [|apply Forall_nil]. apply Forall_cons; [|apply Forall_nil].
    destruct (Hw eq_refl) as (_ & Hrw & Hamw & _ & _).
    apply (cw_shent_ra W2 mem2 E 35 (F + 32 + o) 1 Hrw Hamw ltac:(lia) ltac:(lia) ltac:(lia) E35 E32).
Qed.
End s.
