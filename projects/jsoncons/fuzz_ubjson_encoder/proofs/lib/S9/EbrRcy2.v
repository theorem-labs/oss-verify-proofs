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
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import ArtMem ArtRegs ArtAtomics ArtTac EbtLeaf EbtAllocG EbtPoison EbtPoisonRun ArtRuns ArtRunsMem EbtMmapFixed EbtPopulate1 EbtPopulate2 EbtPopulate3 EbtFp EbtClsPop1 EbtClsPop2.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_rta_Cm1 : forall regs (M rom : word -> option byte) (sp r c spb qs total mfa kf q rr addr2 : Z),
  addr2 = spb + c * 2 ^ 32 + 3758096384 + mfa ->
  getr regs 1 = (0x563a4 : bv 64)%bv -> getr regs 2 = Z_to_bv 64 (sp - 64) -> getr regs 10 = Z_to_bv 64 1321624 -> getr regs 11 = Z_to_bv 64 r ->
  getr regs 12 = Z_to_bv 64 (spb + c * 2 ^ 32) -> getr regs 13 = Z_to_bv 64 total ->
  0x69c000 + 512 <= sp -> sp < 2 ^ 47 -> 1 <= c <= 30 -> 0x69c000 <= r -> r + 128 <= sp - 512 -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> spb = 65536 * qs ->
  0 <= total -> 0 <= mfa < 4 * total -> mfa = 262144 * kf -> 4 * total + 262143 = 262144 * q + rr -> 0 <= rr < 262144 -> 262144 * q <= 536870912 ->
  wrA M (sp - 512) 448 ->
  cellA M (r + 24) 8 mfa -> cellA M (1321624 + 56) 1 0 ->
  cellA M 0x13d8a8 8 0x1d5ba0 -> cellA M 0x1d5ba0 8 4096 -> cellA M 0x13d8b8 8 0x1d7c28 -> cellA M (0x1d7c28 + 260) 1 0 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x56568 : word) M rom) (mkst regs' (0x8ce2c : word) M' rom)
    /\ art_mmap_args regs' addr2 (262144 * q - mfa) 50
    /\ getr regs' 1 = Z_to_bv 64 0x8ebec /\ getr regs' 2 = Z_to_bv 64 (sp - 112 - 128) /\ getr regs' 8 = Z_to_bv 64 (262144 * q - mfa)
    /\ (forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(sp - 512, 448)] M M'
    /\ cellA M' (sp - 64 - 8) 8 0x563a4 /\ cellA M' (sp - 64 - 16) 8 (U (getr regs 8)) /\ cellA M' (sp - 64 - 24) 8 (U (getr regs 9))
    /\ cellA M' (sp - 64 - 32) 8 (U (getr regs 18)) /\ cellA M' (sp - 64 - 40) 8 (U (getr regs 19))
    /\ cellA M' (sp - 112 - 8) 8 0x56608 /\ cellA M' (sp - 112 - 16) 8 (262144 * q) /\ cellA M' (sp - 112 - 24) 8 addr2 /\ cellA M' (sp - 112 - 32) 8 (262144 * q - mfa)
    /\ cellA M' (sp - 112 - 40) 8 0x96da4 /\ cellA M' (sp - 112 - 48) 8 (262144 * q - mfa) /\ cellA M' (sp - 112 - 56) 8 addr2 /\ cellA M' (sp - 112 - 64) 8 (262144 * q - mfa)
    /\ cellA M' (sp - 112 - 72) 8 r /\ cellA M' (sp - 112 - 80) 8 (U (getr regs 20)).
Proof.
  intros regs M rom sp r c spb qs total mfa kf q rr addr2 Haddr2 H1 H2 H10 H11 H12 H13 IMG Hsp' Hc Hr Hr' Hspb Hspb' Espb Htot Hmfa Emfa Eq Hrr Hq W Cmfa Cpm Cpg1 Cpg2 Ccf Cdec.
  pose proof (art_efas_a_fn regs M rom (0x563a4 : bv 64)%bv (sp - 64) 1321624 r (spb + c * 2 ^ 32) total mfa q rr H1 H2 H10 H11 H12 H13
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hr ltac:(lia) ltac:(lia) ltac:(lia) Htot Hmfa Eq Hrr Hq
                ltac:(unfold apart; lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Cmfa Cpm) as RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN1; set (M1 := MM) in RUN1 end.
  assert (A1 : art_agree [(sp - 512, 448)] M M1). { unfold M1, art_efas_frame. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G1 : mem_grows M M1) by (unfold M1, art_efas_frame; zgrows).
  assert (Hq1 : kf + 1 <= q) by lia.
  assert (Ha4 : addr2 mod 4096 = 0).
  { rewrite Haddr2, Espb, Emfa. replace (65536 * qs + c * 2 ^ 32 + 3758096384 + 262144 * kf) with (4096 * (16 * qs) + c * 2 ^ 32 + 3758096384 + 4096 * (64 * kf)) by lia. apply art_mod4096_lin2. }
  assert (Hl4 : (262144 * q - mfa) mod 4096 = 0). { rewrite Emfa. replace (262144 * q - 262144 * kf) with ((64 * (q - kf)) * 4096) by lia. apply Z_mod_mult. }
  pose proof (art_rar_map_pre_fn r1 M1 rom (0x56608 : bv 64)%bv (sp - 112) addr2 (262144 * q - mfa) 105549 0x1d7c28 0
                ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; f_equal; lia) ltac:(unfold r1; gres; f_equal; lia) ltac:(unfold r1; gres; f_equal; lia)
                ltac:(unfold r1; gres; reflexivity)
                ltac:(lia) ltac:(lia) ltac:(lia) Ha4 ltac:(lia) Hl4 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)
                ltac:(eapply wr_grows; [exact G1|]; eapply wr_sub; [exact W|lia|lia])
                ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr)) as RUN2.
  match type of RUN2 with msteps _ _ (mkst ?R _ ?MM _) => set (r2 := R) in RUN2; set (M2 := MM) in RUN2 end.
  assert (A2 : art_agree [(sp - 512, 400)] M1 M2).
  { intros x Hx. cbn in Hx. destruct Hx as [Hx _]. unfold M2. apply art_rar_map_mem_agree; [lia|lia|lia]. }
  assert (G2 : mem_grows M1 M2) by (apply art_rar_map_mem_grows).
  destruct (art_rar_map_mem_cells M1 (sp - 112) (0x56608 : bv 64)%bv r1 addr2 (262144 * q - mfa) 105549 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (F1 & F8 & F9 & F18 & D1 & D8 & D9 & D18 & D19 & D20).
  fold M2 in F1, F8, F9, F18, D1, D8, D9, D18, D19, D20.
  exists r2, M2. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
  split. { unfold art_mmap_args, r2. repeat split; gres; reflexivity. }
  split; [unfold r2; gres; reflexivity|]. split; [unfold r2; gres; reflexivity|]. split; [unfold r2; gres; reflexivity|].
  split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; (unfold r2, r1; gres; reflexivity). }
  split; [eapply mem_grows_trans; [exact G1|exact G2]|].
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A2]|]. zsub. }
  assert (E8 : cellA M1 (sp - 64 - 8) 8 0x563a4 /\ cellA M1 (sp - 64 - 16) 8 (U (getr regs 8)) /\ cellA M1 (sp - 64 - 24) 8 (U (getr regs 9))
               /\ cellA M1 (sp - 64 - 32) 8 (U (getr regs 18)) /\ cellA M1 (sp - 64 - 40) 8 (U (getr regs 19))).
  { unfold M1, art_efas_frame. repeat split; zcell. }
  destruct E8 as (E1 & E8 & E9 & E18 & E19).
  split; [ztr|]. split; [ztr|]. split; [ztr|]. split; [ztr|]. split; [ztr|].
  split; [exact F1|].
  assert (X8 : U (getr r1 8) = 262144 * q). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
  assert (X9 : U (getr r1 9) = addr2). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
  assert (X18 : U (getr r1 18) = 262144 * q - mfa). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
  assert (X19 : U (getr r1 19) = r). { unfold r1; gres. rewrite art_u_lit by lia. lia. }
  assert (X20 : getr r1 20 = getr regs 20). { unfold r1; gres. reflexivity. }
  rewrite X8 in F8. rewrite X9 in F9. rewrite X18 in F18, D18. rewrite X19 in D19. rewrite X20 in D20.
  split; [exact F8|]. split; [exact F9|]. split; [exact F18|].
  split; [exact D1|]. split; [exact D8|]. split; [exact D9|]. split; [exact D18|]. split; [exact D19|]. exact D20.
Qed.

#[using="Type"] Lemma art_rta_Cm2 : forall regs (M rom : word -> option byte) (sp tp key tsd ctx t r c spb qs mfa kf q m1 m2 addr2 len2 shb2 : Z) (g8 g9 g18 g19 g20 : word),
  addr2 = spb + c * 2 ^ 32 + 3758096384 + mfa -> len2 = 262144 * q - mfa -> shb2 = 2147450880 + 8192 * qs + c * 2 ^ 29 + 469762048 + 32768 * kf ->
  getr regs 1 = Z_to_bv 64 0x8ebec -> getr regs 2 = Z_to_bv 64 (sp - 112 - 128) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 len2 -> getr regs 10 = Z_to_bv 64 addr2 ->
  0x69c000 + 512 <= sp -> sp < 2 ^ 47 -> 1 <= c <= 30 -> spb = 65536 * qs -> mfa = 262144 * kf -> 0 <= kf -> kf + 1 <= q -> 262144 * q <= 536870912 ->
  kHighMemBeg <= spb -> spb + 2 ^ 37 < 2 ^ 47 ->
  0 <= m1 < 2 ^ 64 -> 0 <= m2 < 2 ^ 64 ->
  4096 <= t -> t + 4096 <= sp - 512 -> 0x69c000 <= r -> r + 128 <= sp - 512 -> apart t 4096 r 128 ->
  0x10100 <= tp -> tp + 8 <= 0x69c000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x69c000 -> 4096 <= ctx -> ctx + 4096 <= sp - 512 ->
  apart shb2 (32768 * (q - kf)) t 4096 -> apart shb2 (32768 * (q - kf)) r 128 -> apart shb2 (32768 * (q - kf)) ctx 4096 -> shb2 + 32768 * (q - kf) <= sp - 512 ->
  wrA M (sp - 512) 400 -> wrA M shb2 (32768 * (q - kf)) -> wrA M (t + 2872) 16 -> wrA M r 128 ->
  art_layout M -> art_tsd M tp key tsd ctx t ->
  cellA M (sp - 64 - 8) 8 0x563a4 -> cellA M (sp - 64 - 16) 8 (U g8) -> cellA M (sp - 64 - 24) 8 (U g9) -> cellA M (sp - 64 - 32) 8 (U g18) -> cellA M (sp - 64 - 40) 8 (U g19) ->
  cellA M (sp - 112 - 8) 8 0x56608 -> cellA M (sp - 112 - 16) 8 (262144 * q) -> cellA M (sp - 112 - 24) 8 addr2 -> cellA M (sp - 112 - 32) 8 len2 ->
  cellA M (sp - 112 - 40) 8 0x96da4 -> cellA M (sp - 112 - 48) 8 len2 -> cellA M (sp - 112 - 56) 8 addr2 -> cellA M (sp - 112 - 64) 8 len2 ->
  cellA M (sp - 112 - 72) 8 r -> cellA M (sp - 112 - 80) 8 (U g20) ->
  cellA M 0x13d8b8 8 0x1d7c28 -> cellA M (0x1d7c28 + 144) 8 0 ->
  cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x8ce30 : word) M rom) (mkst regs' (0x563a4 : word) M' rom)
    /\ getr regs' 10 = Z_to_bv 64 1 /\ getr regs' 2 = Z_to_bv 64 (sp - 64)
    /\ getr regs' 8 = g8 /\ getr regs' 9 = g9 /\ getr regs' 18 = g18 /\ getr regs' 19 = g19 /\ getr regs' 20 = g20
    /\ (forall x : reg, In x [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(sp - 512, 400); (shb2, 32768 * (q - kf)); (t + 2872, 16); (r + 24, 8)] M M'
    /\ cellA M' (t + 2872) 8 (m1 + 1) /\ cellA M' (t + 2880) 8 (m2 + len2) /\ cellA M' (r + 24) 8 (262144 * q).
Proof.
  intros regs M rom sp tp key tsd ctx t r c spb qs mfa kf q m1 m2 addr2 len2 shb2 g8 g9 g18 g19 g20 Haddr2 Hlen2 Hshb2 H1 H2 H4 H8 H10 IMG Hsp' Hc Espb Emfa Hkf Hq1 Hq Hspb Hspb'
         Hm1 Hm2 Ht Ht' Hr Hr' Atr Htp Htp' Htsd Htsd' Hctx Hctx' Ast Asr Asc Hshsp W Wsh Wts Wr L T E1 E8 E9 E18 E19 F1 F8 F9 F18 D1 D8 D9 D18 D19 D20 Ccf Clim Cm1 Cm2.
  unfold kHighMemBeg in Hspb.
  assert (Eshb : SB + addr2 / 8 = shb2). { rewrite Haddr2, Hshb2. unfold SB. rewrite Espb, Emfa, art_div8_lin2. lia. }
  assert (El8 : len2 / 8 = 32768 * (q - kf)). { rewrite Hlen2, Emfa. replace (262144 * q - 262144 * kf) with ((32768 * (q - kf)) * 8) by lia. apply Z_div_mult. lia. }
  assert (Hl8 : len2 mod 8 = 0). { rewrite Hlen2, Emfa. replace (262144 * q - 262144 * kf) with ((32768 * (q - kf)) * 8) by lia. apply Z_mod_mult. }
  assert (UB : forall w : word, 0 <= U w < 2 ^ 64). { intros w. pose proof (bv_unsigned_in_range 64 w) as R. change (bv_modulus 64) with (2 ^ 64) in R. exact R. }

  pose proof (art_rar_map_post_fn regs M rom (0x56608 : bv 64)%bv (Z_to_bv 64 (262144 * q)) (Z_to_bv 64 addr2) (Z_to_bv 64 len2) (Z_to_bv 64 r) g20
                (Z_to_bv 64 len2) (Z_to_bv 64 addr2) (Z_to_bv 64 len2)
                (sp - 112) len2 addr2 0x1d7c28 H1 H2 H8 H10 ltac:(unfold ret_ok; bveq) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(eapply wr_sub; [exact W|lia|lia])
                ltac:(exact F1) ltac:(rewrite art_u_lit by lia; exact F8) ltac:(rewrite art_u_lit by lia; exact F9) ltac:(rewrite art_u_lit by lia; exact F18)
                ltac:(exact D1) ltac:(rewrite art_u_lit by lia; exact D8) ltac:(rewrite art_u_lit by lia; exact D9)
                ltac:(rewrite art_u_lit by lia; exact D18) ltac:(rewrite art_u_lit by lia; exact D19) ltac:(exact D20)
                Ccf Clim) as RUN1.
  match type of RUN1 with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN1; set (M1 := MM) in RUN1 end.
  assert (A1 : art_agree [(sp - 512, 400)] M M1). { eapply art_agree_sub; [unfold M1; zagree|]. zsub. }
  assert (G1 : mem_grows M M1) by (unfold M1; zgrows).

  pose proof (art_efas_b_fn r1 M1 rom addr2 len2 ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(lia)) as RUN2.
  match type of RUN2 with msteps _ _ (mkst ?R _ _ _) => set (r2 := R) in RUN2 end.

  assert (L1 : art_layout M1). { eapply art_layout_fp; [exact A1| |exact L]. intros z Hz. cbn. repeat split; lia. }
  destruct (art_poison_hi_run r2 M1 rom (0x56624 : bv 64)%bv (sp - 112) addr2 len2 250
              ltac:(unfold r2; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r2, r1; gres; reflexivity) ltac:(unfold r2; gres; reflexivity)
              ltac:(unfold r2; gres; reflexivity) ltac:(unfold r2; gres; reflexivity)
              ltac:(lia) ltac:(lia) ltac:(eapply wr_grows; [exact G1|]; eapply wr_sub; [exact W|lia|lia]) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
              L1 ltac:(unfold kHighMemBeg; lia) ltac:(unfold kHighMemEnd; lia)
              ltac:(rewrite Haddr2, Espb, Emfa; apply art_mod8_lin2) Hl8 ltac:(lia) ltac:(lia) ltac:(intros E; discriminate E)
              ltac:(rewrite Eshb, El8; eapply wr_grows; [exact G1|exact Wsh]))
    as (r3 & RUN3 & P10 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & KP).
  match type of RUN3 with msteps _ _ (mkst _ _ ?MM _) => set (M3 := MM) in RUN3 end.
  assert (A3 : art_agree [(sp - 512, 400); (shb2, 32768 * (q - kf))] M1 M3).
  { unfold M3, art_poison_frame. rewrite Eshb, El8. eapply art_agree_sub; [zagree|]. rewrite Z2Nat.id by lia. zsub. }
  assert (G3 : mem_grows M1 M3) by (unfold M3, art_poison_frame; zgrows).
  assert (A13 : art_agree [(sp - 512, 400); (shb2, 32768 * (q - kf))] M M3). { eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A3]|]. zsub. }
  assert (G13 : mem_grows M M3) by (eapply mem_grows_trans; eassumption).
  assert (Hqs : 0 <= qs) by lia.
  assert (T3 : art_tsd M3 tp key tsd ctx t).
  { eapply art_tsd_fp; [exact A13| | |exact Htp|exact Htp'|exact Htsd|exact Htsd'|exact T].
    - intros z Hz. cbn. repeat split; lia.
    - intros z Hz. cbn. unfold apart in Asc. repeat split; lia. }
  assert (R3_4 : getr r3 4 = Z_to_bv 64 tp). { rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E). unfold r2, r1; gres. exact H4. }
  assert (R3_8 : getr r3 8 = Z_to_bv 64 (262144 * q)). { rewrite P8. unfold r2, r1; gres. reflexivity. }
  assert (R3_18 : getr r3 18 = Z_to_bv 64 len2). { rewrite P18. unfold r2, r1; gres. reflexivity. }
  assert (R3_19 : getr r3 19 = Z_to_bv 64 r). { rewrite P19. unfold r2, r1; gres. reflexivity. }
  unfold apart in Ast, Asr, Atr.
  pose proof (art_efas_c_fn r3 M3 rom (0x563a4 : bv 64)%bv (sp - 64) tp key tsd ctx t r (262144 * q) len2 m1 m2 (U g8) (U g9) (U g18) (U g19)
                ltac:(rewrite P2; f_equal; lia) R3_4 R3_8 R3_18 R3_19
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(unfold ret_ok; bveq)
                Hm1 Hm2 ltac:(lia) ltac:(lia) (UB g8) (UB g9) (UB g18) (UB g19)
                ltac:(eapply wr_grows; [exact G13|]; eapply wr_sub; [exact W|lia|lia]) T3
                ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; destruct T as (_ & _ & _ & _ & _ & _ & _ & Hk & _); lia) ltac:(unfold apart; lia)
                ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
                ltac:(eapply wr_grows; [exact G13|exact Wts]) ltac:(eapply wr_grows; [exact G13|exact Wr])
                ltac:(ztr) ltac:(ztr) ltac:(change (U (0x563a4 : bv 64)%bv) with 0x563a4; ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr)) as RUN4.
  match type of RUN4 with msteps _ _ (mkst ?R _ ?MM _) => set (r4 := R) in RUN4; set (M4 := MM) in RUN4 end.
  assert (A4 : art_agree [(sp - 512, 400); (t + 2872, 16); (r + 24, 8)] M3 M4).
  { unfold M4, art_efas_c_mem. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G4 : mem_grows M3 M4) by (unfold M4, art_efas_c_mem; zgrows).
  exists r4, M4. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3|exact RUN4]|].
  split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|].
  split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|].
  split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|]. split; [unfold r4; gres; apply Z_to_bv_bv_unsigned|].
  split; [unfold r4; gres; rewrite P20; unfold r2, r1; gres; reflexivity|].
  split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end;
           first [ unfold r4; gres; rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E); unfold r2, r1; gres; reflexivity
                 | unfold r4; gres; rewrite P21; unfold r2, r1; gres; reflexivity ]. }
  split; [eapply mem_grows_trans; [exact G13|exact G4]|].
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A13|exact A4]|]. zsub. }
  unfold M4, art_efas_c_mem.
  split; [zcell|]. split; [zcell|]. zcell.
Qed.

End FPX.
