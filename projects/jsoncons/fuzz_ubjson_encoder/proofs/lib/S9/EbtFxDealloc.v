(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import As0Tables.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac EbtLeaf EbtPoison EbtAllocG EbtUnwind EbtFree1.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import EbtHdrW.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Eb0_code_r5fac4_60344 Eb0_code_r67bcc_67d3c Eb0_code_r3cf10_3de98 Eb0_code_r41498_42984.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).
Set Printing Depth 1000080. Set Printing Width 10000.
Ltac showst := lazymatch goal with |- msteps _ (mkst ?R ?P ?MM _) _ => idtac "REGS" R; idtac "PC" P; idtac "MEM" MM | |- ?G => idtac "GOAL" G end; fail "SHOWST".

Ltac zlhu F D a HYP :=
  chain_step; [reflexivity | eapply step_lhu; [exact F | reflexivity | exact D | zaddr a; exact HYP | apply art_bytes2; lia ] | step_simpl; vnorm].

Lemma art_fx_zb_or : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> v_or (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.lor x y).
Proof. intros x y Hx Hy. unfold v_or. rewrite !art_u_lit by lia. reflexivity. Qed.

Definition art_fx_fcu2_mem (M : word -> option byte) (S p b1 n sz t fr1 fr2 f22 f23 f24 : Z) : word -> option byte :=
  (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 4 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 8 (Wn 1 M (t + 3168) 0) (S - 2136) 502648) (S - 2144) S) (S - 2152) p) (S - 2160) 502536) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2184) (S - 81)) (S - 2192) f22) (S - 2192 - 8) 340780) (S - 2192 - 16) (S - 2128)) (S - 2192 - 24) p) (p - 16) (3 + 256 * b1)) (p - 16 + 16) (2 ^ 64 - 2 ^ 32)) (S - 2192 - 8) 341272) (S - 2192 - 24) 539752) (t + 2800 + 24) (fr1 + 1)) (t + 2800 + 32) (n + fr2)) (S - 2136) 502648) (S - 2144) S) (S - 2152) p) (S - 2160) 502536) (S - 2168) 1) (S - 2176) (S - 2128)) (S - 2176 - 8) 358520).

Section FPX. Context {fx : PropExec.FPState}.

#[local] Ltac wpc := lazymatch goal with |- msteps _ (mkstr _ ?p _ _ _) _ => wlit p | |- msteps _ (mkst _ ?p _ _) _ => wlit p end.

#[using="Type"] Lemma art_cas23W_fn : forall regs (M rom : word -> option byte) (m b1 : Z),
  getr regs 18 = Z_to_bv 64 m -> 16 <= m -> m + 16 < 2 ^ 47 -> m mod 16 = 0 -> 0 <= b1 < 2 ^ 23 ->
  cellA M m 4 (2 + 256 * b1) -> wrA M m 4 ->
  msteps ASEGS (mkst regs (0x53368 : word) M rom)
    (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 (m * 2 ^ 3))) 11 (Z_to_bv 64 3)) 12 (Z_to_bv 64 (2 + 256 * b1))) 13 (Z_to_bv 64 m)) 14 (Z_to_bv 64 2)) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0))
          (0x533a8 : word) (Wn 4 M m (3 + 256 * b1)) rom).
Proof.
  intros regs M rom m b1 H18 Hm Hm' Hm16 Hb1 Chw Whw.
  assert (Hm4 : m mod 4 = 0). { pose proof (Z.div_mod m 16 ltac:(lia)) as E. rewrite Hm16 in E. rewrite E. replace (16 * (m / 16) + 0) with ((4 * (m / 16)) * 4) by lia. apply Z_mod_mult. }
  stepn F_53318 D_53318. rwH. unfold v_andi. rewrite art_u_lit by lia. change (bv_wrap 64 (-4)) with 18446744073709551612. rewrite art_land_m4 by lia.
  replace (m / 4 * 4) with m by (pose proof (Z.div_mod m 4 ltac:(lia)); lia).
  stepn F_5331c D_5331c. rwH. rewrite art_zb_slli by lia.
  zstep F_53320 D_53320. zstep F_53324 D_53324. zstep F_53328 D_53328.
  stepn F_5332c D_5332c. rwH. rewrite art_sllw_0 by lia.
  stepn F_53330 D_53330. rwH. rewrite art_sllw_0 by lia.
  stepn F_53334 D_53334. rwH. rewrite art_sllw_0 by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Whw' : wok AsanUbsan.M.loaded_segments X m 4) by (rewok Whw) end.

  chain_step; [reflexivity
    | eapply (art_step_lr_w _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m) _ (Z_to_bv 64 (2 + 256 * b1)));
      [exact F_53338 | reflexivity | exact D_53338 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4
      | exact Chw | apply art_bytes4; lia ]
    | ]. wpc. rewrite art_v_lw_small by lia.

  chain_step; [reflexivity | eapply art_step_and_r; [exact F_5333c | reflexivity | exact D_5333c | reflexivity] | ]. wpc.
  gres. rewrite (art_zb_and (2 + 256 * b1) 255) by lia.
  replace (Z.land (2 + 256 * b1) 255) with 2.
  2:{ change 255 with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256. replace (2 + 256 * b1) with (2 + b1 * 256) by lia. rewrite Z_mod_plus_full. reflexivity. }
  chain_step; [reflexivity
    | eapply art_step_branch_ft_r; [exact F_53340 | reflexivity | exact D_53340 | cbn [Sem.branch_taken]; gres; rwH; unfold bv_eqb; rewrite Z.eqb_refl; reflexivity ]
    | ]. wpc.

  chain_step; [reflexivity | eapply art_step_xor_r; [exact F_53344 | reflexivity | exact D_53344 | reflexivity] | ]. wpc.
  chain_step; [reflexivity | eapply art_step_and_r; [exact F_53348 | reflexivity | exact D_53348 | reflexivity] | ]. wpc.
  chain_step; [reflexivity | eapply art_step_xor_r; [exact F_5334c | reflexivity | exact D_5334c | reflexivity] | ]. wpc.
  gres.
  rewrite (art_casw_xor 2 3 b1) by lia.

  chain_step; [reflexivity
    | eapply (art_step_sc_w_ok _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 m));
      [exact F_53350 | reflexivity | exact D_53350 | reflexivity | gres; rwH; reflexivity | rewrite art_u_lit by lia; exact Hm4 | gres; rwH; reflexivity
      | exact Whw' ]
    | ]. wpc.
  change (wbytes ?M0 (Z_to_bv 64 m) (word_to_le_bytes 4 (Z_to_bv 64 (3 + 256 * b1)))) with (Wn 4 M0 m (3 + 256 * b1)).
  zbft F_53354 D_53354.
  zret.
Qed.

#[using="Type"] Lemma art_fx_fcu2W_fn : forall regs (M rom : word -> option byte) (S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> getr regs 4 = Z_to_bv 64 tp ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x69c000 + 16 <= p -> p + 8 < 2 ^ 47 -> p mod 16 = 0 -> 0 <= b1 < 2 ^ 24 -> b1 mod 4 = 1 -> 1 <= n < 2 ^ 40 -> b1 / 256 = n / 2 ^ 32 -> 1 <= sz <= 30 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> apart (p - 16) 24 (S - 4096) 8192 -> apart (p - 16) 24 t 4096 ->
  apart ctx 4096 (S - 4096) 8192 -> apart t 4096 ctx 4096 -> apart (p - 16) 24 ctx 4096 -> hid (ctx + 4096 <= 0x10000 \/ 0x69c000 <= ctx) -> hid (t + 4096 <= 0x10000 \/ 0x69c000 <= t) ->
  0x10100 <= tp -> tp + 8 <= 0x69c000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x69c000 ->
  0 <= fr1 < 2 ^ 64 -> 0 <= fr2 < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> wrA M (p - 16) 24 -> art_tsd M tp key tsd ctx t ->
  cellA M (S - 2136) 8 0x7ab64 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x7ab08 : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 2128) 8 (S - 2112) -> cellA M (S - 2120) 8 sz ->
  cellA M (p - 16) 4 (2 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M 0x1d7bc8 8 0 -> cellA M t 8 ctx -> cellA M (ctx + 8) 4 0 -> cellA M (t + 2824) 8 fr1 -> cellA M (t + 2832) 8 fr2 ->
  msteps ASEGS (mkst regs (0x83144 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x57898 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (p - 16))) 9 (Z_to_bv 64 (S - 2128))) 10 (Z_to_bv 64 (S - 2112))) 11 (Z_to_bv 64 sz)) 12 (Z_to_bv 64 (S - 2112))) 13 (Z_to_bv 64 ctx)) 14 (Z_to_bv 64 (fr1 + 1))) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0)) 18 (Z_to_bv 64 1321624)) 19 (Z_to_bv 64 0)) 20 (Z_to_bv 64 t)) 21 (Z_to_bv 64 (S - 81))) 22 (Z_to_bv 64 f22)) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x9b170 : word) (art_fx_fcu2_mem M S p b1 n sz t fr1 fr2 f22 f23 f24) rom).
Proof.
  intros regs M rom S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 H2 H24 H4 HS HS' Hp Hp' Hp16 Hb1 Hb14 Hn Hlink Hsz Ht Ht' Atsp Apsp Apt Actx Atctx Apctx Cimg Timg
         Htp0 Htp1 Htsd0 Htsd Hfr1 Hfr2 Hf22 Hf23 Hf24 W Wt Wp TSD C36 C44 C52 C60 C68 C76 C84 C92 C00 C08 C28 C20 Chw Cn Cfh Ctctx Ctid Cfr1 Cfr2.
  pose proof TSD as (Ttsd1 & Ttsd2 & Ttsd3 & Ttsd4 & Ttsd5 & TR). pose proof Timg as Timg'; unfold hid in Timg'.
  assert (Hb1w := Hb1). clear Hb1. assert (Hb1 : 0 <= b1 < 2 ^ 16) by (apply (art_b1_bound b1 n (proj1 Hb1w) Hlink); clear - Hn; lia). clear Hb1w.
  assert (Hhi : 0 <= b1 / 256 < 2 ^ 15) by (split; [apply Z.div_pos; lia|apply Z.div_lt_upper_bound; lia]).
  assert (Hlo : 0 <= n mod 2 ^ 32 < 2 ^ 32) by (apply Z.mod_pos_bound; lia). assert (Htb : 0 <= b1 mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  assert (Hhi32 : 0 <= b1 / 256 * 2 ^ 32 < 2 ^ 47) by lia.

  zsb F_830f4 D_830f4 (t + 2047 + 1121) 0 ltac:(rewok Wt). replace (t + 2047 + 1121) with (t + 3168) by lia.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (D36 : cellA X (S - 2136) 8 0x7ab64) by zcell; assert (D44 : cellA X (S - 2144) 8 S) by zcell; assert (D52 : cellA X (S - 2152) 8 p) by zcell;
    assert (D60 : cellA X (S - 2160) 8 (U (0x7ab08 : bv 64)%bv)) by zcell; assert (D68 : cellA X (S - 2168) 8 1) by zcell;
    assert (D76 : cellA X (S - 2176) 8 (S - 2128)) by zcell; assert (D84 : cellA X (S - 2184) 8 (S - 81)) by zcell;
    assert (D92 : cellA X (S - 2192) 8 f22) by zcell; assert (D00 : cellA X (S - 2200) 8 f23) by zcell; assert (D08 : cellA X (S - 2208) 8 f24) by zcell end.
  zld F_830f8 D_830f8 (S - 2136) D36. zld F_830fc D_830fc (S - 2144) D44. zld F_83100 D_83100 (S - 2152) D52. zld F_83104 D_83104 (S - 2160) D60.
  zld F_83108 D_83108 (S - 2168) D68. zld F_8310c D_8310c (S - 2176) D76. zld F_83110 D_83110 (S - 2184) D84. zld F_83114 D_83114 (S - 2192) D92.
  zld F_83118 D_83118 (S - 2200) D00. zld F_8311c D_8311c (S - 2208) D08.
  zstep F_83120 D_83120.
  stepjr F_83124 D_83124 (0x7ab64 : bv 64)%bv ltac:(gres; bveq).

  zstep F_7ab14 D_7ab14. zstep F_7ab18 D_7ab18. zstep F_7ab1c D_7ab1c. zstep F_7ab20 D_7ab20.
  stepn F_7ab24 D_7ab24.
  zstep F_53268 D_53268. zstep F_5326c D_5326c. zstep F_53270 D_53270. zstep F_53274 D_53274. zstep F_53278 D_53278. zstep F_5327c D_5327c.
  zstep F_53280 D_53280. zstep F_53284 D_53284. zstep F_53288 D_53288.
  stepn F_5328c D_5328c.

  zstep F_53290 D_53290.
  zsd F_53294 D_53294 (S - 2136) (U (0x7ab78 : bv 64)%bv) ltac:(rewok W). zsd F_53298 D_53298 (S - 2144) S ltac:(rewok W). zsd F_5329c D_5329c (S - 2152) p ltac:(rewok W).
  zsd F_532a0 D_532a0 (S - 2160) (U (0x7ab08 : bv 64)%bv) ltac:(rewok W). zsd F_532a4 D_532a4 (S - 2168) 1 ltac:(rewok W). zsd F_532a8 D_532a8 (S - 2176) (S - 2128) ltac:(rewok W).
  zsd F_532ac D_532ac (S - 2184) (S - 81) ltac:(rewok W). zsd F_532b0 D_532b0 (S - 2192) f22 ltac:(rewok W).
  zbft F_532b4 D_532b4.
  zstep F_532b8 D_532b8. zstep F_532bc D_532bc. zstep F_532c0 D_532c0. zstep F_532c4 D_532c4. zstep F_532c8 D_532c8. zstep F_532cc D_532cc. zstep F_532d0 D_532d0. zstep F_532d4 D_532d4.
  stepn F_532d8 D_532d8.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Cfh' : cellA X 0x1d7bc8 8 0) by (unfold hid in Timg; zcell) end.
  zcall (art_run_free_hooks_fn _ _ _ _ (S - 2192)).
  zbtk F_532dc D_532dc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ => assert (Chw' : cellA X (p - 16) 4 (2 + 256 * b1)) by zcell; assert (Wp' : wrA X (p - 16) 24) by zwr end.
  assert (Hm16 : (p - 16) mod 16 = 0) by (replace (p - 16) with (p + (-1) * 16) by lia; rewrite Z_mod_plus_full; exact Hp16).
  zcall (art_cas23W_fn _ _ _ (p - 16) b1).
  zstep F_53358 D_53358. zstep F_5335c D_5335c.
  zsd F_53360 D_53360 (p - 16 + 16) (2 ^ 64 - 2 ^ 32) ltac:(rewok Wp).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw) as (Cst & Cb1 & Chi) end.
  replace ((3 + 256 * b1) mod 256) with 3 in Cst by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity).
  rewrite (art_hdrw_tb 3 b1) in Cb1 by lia.
  rewrite (art_hdrw_hi 3 b1) in Chi by lia.
  zlbu F_53364 D_53364 (p - 16 + 1) Cb1.
  stepn F_53368 D_53368. rwH. rewrite art_zb_andi by lia. replace (Z.land (b1 mod 256) 3) with 1 by (rewrite art_land3_mod256 by lia; symmetry; exact Hb14).
  zbft F_5336c D_5336c.
  stepn F_53370 D_53370. rwH. unfold v_andi. rewrite art_u_lit by lia. change (Z_to_bv 64 (Z.land 1 (bv_wrap 64 (-2)))) with (Z_to_bv 64 0 : word).
  zstep F_53374 D_53374.
  zbtk F_53378 D_53378.
  stepn F_534c4 D_534c4.
  zcall (art_thread_stats_fn _ _ _ _ (S - 2192) tp key tsd ctx t).
  { unfold art_tsd. repeat split; try lia; zcell. }
  all: try (unfold apart; lia). all: try (unfold apart in Actx; unfold apart; lia).
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw2 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw2) as (_ & _ & Chi');
    rewrite (art_hdrw_hi 3 b1) in Chi' by lia; replace (p - 16 + 2) with (p - 14) in Chi' by lia;
    assert (Cn' : cellA X (p - 12) 4 (n mod 2 ^ 32)) by (apply cell4_mod; zcell);
    assert (Cfr1' : cellA X (t + 2800 + 24) 8 fr1) by (replace (t + 2800 + 24) with (t + 2824) by lia; zcell);
    assert (Cfr2' : cellA X (t + 2800 + 32) 8 fr2) by (replace (t + 2800 + 32) with (t + 2832) by lia; zcell) end.
  zlhu F_534c8 D_534c8 (p - 14) Chi'.
  zlwu F_534cc D_534cc (p - 12) Cn'.
  zld F_534d0 D_534d0 (t + 2800 + 32) Cfr2'. zld F_534d4 D_534d4 (t + 2800 + 24) Cfr1'.
  zstep F_534d8 D_534d8.
  stepn F_534dc D_534dc. rwH. rewrite art_fx_zb_or by lia. rewrite (art_or_b1lo b1 n) by lia.
  zstep F_534e0 D_534e0. zstep F_534e4 D_534e4.
  zsd F_534e8 D_534e8 (t + 2800 + 24) (fr1 + 1) ltac:(rewok Wt).
  zsd F_534ec D_534ec (t + 2800 + 32) (n + fr2) ltac:(rewok Wt).
  zstep F_534f0 D_534f0. zstep F_534f4 D_534f4. zstep F_534f8 D_534f8. zstep F_534fc D_534fc.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (E36 : cellA X (S - 2136) 8 (U (0x7ab78 : bv 64)%bv)) by zcell; assert (E44 : cellA X (S - 2144) 8 S) by zcell;
    assert (E52 : cellA X (S - 2152) 8 p) by zcell; assert (E60 : cellA X (S - 2160) 8 (U (0x7ab08 : bv 64)%bv)) by zcell;
    assert (E68 : cellA X (S - 2168) 8 1) by zcell; assert (E76 : cellA X (S - 2176) 8 (S - 2128)) by zcell;
    assert (E84 : cellA X (S - 2184) 8 (S - 81)) by zcell; assert (E92 : cellA X (S - 2192) 8 f22) by zcell end.
  zld F_53500 D_53500 (S - 2136) E36. zld F_53504 D_53504 (S - 2144) E44. zld F_53508 D_53508 (S - 2152) E52. zld F_5350c D_5350c (S - 2160) E60.
  zld F_53510 D_53510 (S - 2168) E68. zld F_53514 D_53514 (S - 2176) E76. zld F_53518 D_53518 (S - 2184) E84. zld F_5351c D_5351c (S - 2192) E92.
  zstep F_53520 D_53520.
  stepn F_53524 D_53524.

  zstep F_577f0 D_577f0.
  zsd F_577f4 D_577f4 (S - 2136) (U (0x7ab78 : bv 64)%bv) ltac:(rewok W). zsd F_577f8 D_577f8 (S - 2144) S ltac:(rewok W). zsd F_577fc D_577fc (S - 2152) p ltac:(rewok W).
  zsd F_57800 D_57800 (S - 2160) (U (0x7ab08 : bv 64)%bv) ltac:(rewok W). zsd F_57804 D_57804 (S - 2168) 1 ltac:(rewok W). zsd F_57808 D_57808 (S - 2176) (S - 2128) ltac:(rewok W).
  zstep F_5780c D_5780c.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Hhw3 : cellA X (p - 16) 4 (3 + 256 * b1)) by zcell;
    destruct (cell4_split X (p - 16) (3 + 256 * b1) ltac:(lia) ltac:(lia) ltac:(lia) Hhw3) as (Cst' & _ & _);
    replace ((3 + 256 * b1) mod 256) with 3 in Cst' by (replace (3 + 256 * b1) with (3 + b1 * 256) by lia; rewrite Z_mod_plus_full; reflexivity) end.
  zlb F_57810 D_57810 (p - 16) Cst'.
  zstep F_57814 D_57814.
  zbft F_57818 D_57818.
  zstep F_5781c D_5781c. zstep F_57820 D_57820.
  stepn F_57824 D_57824.
  zcall (art_cur_thread_fn _ _ _ _ (S - 2176) tp key tsd ctx t).
  { unfold art_tsd. repeat split; try lia; zcell. }
  all: try (unfold apart; lia). all: try (unfold apart in Actx; unfold apart; lia).
  zbft F_57828 D_57828.
  match goal with |- msteps _ (mkst _ _ ?X _) _ =>
    assert (Ctctx' : cellA X t 8 ctx) by zcell;
    assert (C28' : cellA X (S - 2128) 8 (S - 2112)) by zcell;
    assert (C20' : cellA X (S - 2128 + 8) 8 sz) by (replace (S - 2128 + 8) with (S - 2120) by lia; zcell);
    assert (Ctid' : cellA X (ctx + 8) 4 0) by zcell end.
  zld F_5782c D_5782c t Ctctx'. zld F_57830 D_57830 (S - 2128) C28'. zld F_57834 D_57834 (S - 2128 + 8) C20'.
  zlw F_57838 D_57838 (ctx + 8) Ctid'.
  zstep F_5783c D_5783c. zstep F_57840 D_57840.
  stepn F_57844 D_57844.
  unfold art_fx_fcu2_mem. zret.
Qed.

#[using="Type"] Lemma art_fx_fcu2_fn : forall regs (M rom : word -> option byte) (S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 : Z),
  getr regs 2 = Z_to_bv 64 (S - 2208) -> getr regs 24 = Z_to_bv 64 (t + 2047) -> getr regs 4 = Z_to_bv 64 tp ->
  0x10007fff8000 + 8192 <= S -> S < 2 ^ 47 -> 0x69c000 + 16 <= p -> p + 8 < 2 ^ 47 -> p mod 16 = 0 -> 0 <= b1 < 256 -> b1 mod 4 = 1 -> 1 <= n < 2 ^ 32 -> 1 <= sz <= 30 ->
  4096 <= t -> t + 4096 < 2 ^ 64 -> apart t 4096 (S - 4096) 8192 -> apart (p - 16) 24 (S - 4096) 8192 -> apart (p - 16) 24 t 4096 ->
  apart ctx 4096 (S - 4096) 8192 -> apart t 4096 ctx 4096 -> apart (p - 16) 24 ctx 4096 -> hid (ctx + 4096 <= 0x10000 \/ 0x69c000 <= ctx) -> hid (t + 4096 <= 0x10000 \/ 0x69c000 <= t) ->
  0x10100 <= tp -> tp + 8 <= 0x69c000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x69c000 ->
  0 <= fr1 < 2 ^ 64 -> 0 <= fr2 < 2 ^ 64 -> 0 <= f22 < 2 ^ 64 -> 0 <= f23 < 2 ^ 64 -> 0 <= f24 < 2 ^ 64 ->
  wrA M (S - 4096) 4096 -> wrA M t 4096 -> wrA M (p - 16) 24 -> art_tsd M tp key tsd ctx t ->
  cellA M (S - 2136) 8 0x7ab64 -> cellA M (S - 2144) 8 S -> cellA M (S - 2152) 8 p -> cellA M (S - 2160) 8 (U (0x7ab08 : bv 64)%bv) -> cellA M (S - 2168) 8 1 ->
  cellA M (S - 2176) 8 (S - 2128) -> cellA M (S - 2184) 8 (S - 81) -> cellA M (S - 2192) 8 f22 -> cellA M (S - 2200) 8 f23 -> cellA M (S - 2208) 8 f24 ->
  cellA M (S - 2128) 8 (S - 2112) -> cellA M (S - 2120) 8 sz ->
  cellA M (p - 16) 4 (2 + 256 * b1) -> cellA M (p - 12) 4 n ->
  cellA M 0x1d7bc8 8 0 -> cellA M t 8 ctx -> cellA M (ctx + 8) 4 0 -> cellA M (t + 2824) 8 fr1 -> cellA M (t + 2832) 8 fr2 ->
  msteps ASEGS (mkst regs (0x83144 : word) M rom) (mkst (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd (regupd regs 1 (0x57898 : bv 64)%bv) 2 (Z_to_bv 64 (S - 2176))) 8 (Z_to_bv 64 (p - 16))) 9 (Z_to_bv 64 (S - 2128))) 10 (Z_to_bv 64 (S - 2112))) 11 (Z_to_bv 64 sz)) 12 (Z_to_bv 64 (S - 2112))) 13 (Z_to_bv 64 ctx)) 14 (Z_to_bv 64 (fr1 + 1))) 15 (Z_to_bv 64 255)) 16 (Z_to_bv 64 3)) 17 (Z_to_bv 64 0)) 18 (Z_to_bv 64 1321624)) 19 (Z_to_bv 64 0)) 20 (Z_to_bv 64 t)) 21 (Z_to_bv 64 (S - 81))) 22 (Z_to_bv 64 f22)) 23 (Z_to_bv 64 f23)) 24 (Z_to_bv 64 f24)) (0x9b170 : word) (art_fx_fcu2_mem M S p b1 n sz t fr1 fr2 f22 f23 f24) rom).
Proof.
  intros regs M rom S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 H2 H24 H4 HS HS' Hp Hp' Hp16 Hb1 Hb14 Hn.
  apply (art_fx_fcu2W_fn regs M rom S p b1 n sz t tp key tsd ctx fr1 fr2 f22 f23 f24 H2 H24 H4 HS HS' Hp Hp' Hp16 ltac:(lia) Hb14 ltac:(lia)).
  rewrite (Z.div_small b1), (Z.div_small n) by lia. reflexivity.
Qed.
End FPX.
