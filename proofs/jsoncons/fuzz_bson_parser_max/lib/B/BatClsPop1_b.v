(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b BatPoisonRun_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatMmapFixed_b BatPopulate1_b BatPopulate2_b BatPopulate3_b BatFp_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia2.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Lemma art_mod4096_lin : forall a b c, (4096 * a + b * 2 ^ 32 + 4096 * c) mod 4096 = 0.
Proof. intros a b c. replace (4096 * a + b * 2 ^ 32 + 4096 * c) with ((a + b * 2 ^ 20 + c) * 4096) by lia. apply Z_mod_mult. Qed.

Section FPX. Context {fx : PropExec.FPState}.

(* [comment removed for export] *)
#[using="Type"] Lemma art_clspop_A : forall regs (M rom : word -> option byte) (raw : word) (sp st c r req spb qs au mu km need : Z),
  getr regs 1 = raw -> getr regs 2 = Z_to_bv 64 sp -> getr regs 10 = Z_to_bv 64 1295832 -> getr regs 11 = Z_to_bv 64 st -> getr regs 12 = Z_to_bv 64 c ->
  getr regs 13 = Z_to_bv 64 r -> getr regs 14 = Z_to_bv 64 req ->
  0x696000 + 464 <= sp -> sp < 2 ^ 47 -> 0 <= st < 2 ^ 64 -> 1 <= c <= 30 -> 0x696000 <= r -> r + 128 < 2 ^ 47 ->
  1 <= req <= 8 -> need = AsanTab.class_size c * req -> 0 <= spb -> spb + 2 ^ 37 < 2 ^ 47 -> spb = 65536 * qs -> mu = 262144 * km ->
  0 <= au -> au <= mu -> mu < au + need -> need <= 2 ^ 18 -> mu + 2 ^ 18 <= 3758096384 ->
  apart (sp - 464) 464 r 128 ->
  wrA M (sp - 464) 464 ->
  cellA M (1295832 + 32) 8 spb -> cellA M (r + 32) 8 au -> cellA M (r + 48) 8 mu -> cellA M (r + 56) 8 0 -> cellA M (1295832 + 56) 1 0 -> cellA M (1295832 + 40) 4 0xffffffff ->
  cellA M 0x1374a0 8 0x1cf6e0 -> cellA M 0x1cf6e0 8 4096 -> cellA M 0x1374b0 8 0x1d1768 -> cellA M (0x1d1768 + 260) 1 0 ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x57894 : word) M rom) (mkst regs' (0x8bc80 : word) M' rom)
    /\ art_mmap_args regs' (spb + c * 2 ^ 32 + mu) 262144 50
    /\ getr regs' 1 = Z_to_bv 64 0x8da40 /\ getr regs' 2 = Z_to_bv 64 (sp - 64 - 128) /\ getr regs' 8 = Z_to_bv 64 262144
    /\ getr regs' 21 = Z_to_bv 64 (AsanTab.class_size c) /\ getr regs' 22 = Z_to_bv 64 1295832
    /\ (forall x : reg, In x [3; 4; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(sp - 464, 464)] M M'
    /\ cellA M' (sp - 8) 8 (U raw) /\ cellA M' (sp - 16) 8 (U (getr regs 8)) /\ cellA M' (sp - 24) 8 (U (getr regs 9)) /\ cellA M' (sp - 32) 8 (U (getr regs 18))
    /\ cellA M' (sp - 40) 8 (U (getr regs 19)) /\ cellA M' (sp - 48) 8 (U (getr regs 20)) /\ cellA M' (sp - 56) 8 (U (getr regs 21)) /\ cellA M' (sp - 64) 8 (U (getr regs 22))
    /\ cellA M' (sp - 64 - 8) 8 0x579b4 /\ cellA M' (sp - 64 - 16) 8 r /\ cellA M' (sp - 64 - 24) 8 st /\ cellA M' (sp - 64 - 32) 8 (spb + c * 2 ^ 32)
    /\ cellA M' (sp - 64 - 40) 8 0x95bf8 /\ cellA M' (sp - 64 - 48) 8 262144 /\ cellA M' (sp - 64 - 56) 8 (spb + c * 2 ^ 32 + mu)
    /\ cellA M' (sp - 64 - 64) 8 (spb + c * 2 ^ 32) /\ cellA M' (sp - 64 - 72) 8 262144 /\ cellA M' (sp - 64 - 80) 8 (spb + c * 2 ^ 32 + mu).      (* [comment removed for export] *)
Proof.
  intros regs M rom raw sp st c r req spb qs au mu km need H1 H2 H10 H11 H12 H13 H14 IMG Hsp' Hst Hc Hr Hr' Hreq Eneed Hspb Hspb' Espb Emu Hau Haumu Hneed Hneed' Hex A W
         Cspb Cau Cmu Cmm Cpm Crel Cpg1 Cpg2 Ccf Cdec.
  destruct (art_pop_a_run regs M rom raw sp 1295832 st c r req spb au mu need 0 H1 H2 H10 H11 H12 H13 H14 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Hst Hc Hr Hr'
              Hreq Eneed Hspb Hspb' Hau Haumu Hneed Hneed' ltac:(lia) ltac:(lia) ltac:(unfold apart in A |- *; lia) ltac:(eapply wr_sub; [exact W|lia|lia]) Cspb Cau Cmu Cmm Cpm Crel)
    as (rA & RUNA & A1 & A2 & A8 & A9 & A11 & A12 & A13 & A18 & A19 & A20 & A21 & A22 & KA).
  set (MF := art_pop_frame M sp raw regs) in *.
  assert (AF : art_agree [(sp - 464, 464)] M MF).
  { eapply art_agree_sub; [unfold MF, art_pop_frame; zagree|]. zsub. }
  assert (GF : mem_grows M MF) by (unfold MF, art_pop_frame; zgrows).
  assert (Haddr : (spb + c * 2 ^ 32 + mu) mod 4096 = 0).
  { rewrite Espb, Emu. replace (65536 * qs + c * 2 ^ 32 + 262144 * km) with (4096 * (16 * qs) + c * 2 ^ 32 + 4096 * (64 * km)) by lia. apply art_mod4096_lin. }
  pose proof (art_rar_map_pre_fn rA MF rom (0x579b4 : bv 64)%bv (sp - 64) (spb + c * 2 ^ 32 + mu) 262144 97009 0x1d1768 0 A1 A2 A11 A12 A13
                ltac:(lia) ltac:(lia) ltac:(lia) Haddr ltac:(lia) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(reflexivity)
                ltac:(eapply wr_grows; [exact GF|]; eapply wr_sub; [exact W|lia|lia])
                ltac:(ztr) ltac:(ztr) ltac:(ztr) ltac:(ztr)) as RUNB.
  set (MB := art_rar_map_mem MF (sp - 64) (0x579b4 : bv 64)%bv rA (spb + c * 2 ^ 32 + mu) 262144 97009) in *.
  assert (AB : art_agree [(sp - 464, 464)] MF MB).
  { intros x Hx. cbn in Hx. destruct Hx as [Hx _]. unfold MB. apply art_rar_map_mem_agree; [lia|lia|lia]. }
  assert (GB : mem_grows MF MB) by (apply art_rar_map_mem_grows).
  destruct (art_rar_map_mem_cells MF (sp - 64) (0x579b4 : bv 64)%bv rA (spb + c * 2 ^ 32 + mu) 262144 97009 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as (F1 & F8 & F9 & F18 & E1 & E8 & E9 & E18 & E19 & E20).
  fold MB in F1, F8, F9, F18, E1, E8, E9, E18, E19, E20.
  eexists. exists MB. split; [eapply msteps_trans; [exact RUNA | exact RUNB]|].
  split. { unfold art_mmap_args. repeat split; gres; reflexivity. }
  split; [gres; reflexivity|]. split; [gres; reflexivity|]. split; [gres; reflexivity|].
  split; [gres; exact A21|]. split; [gres; exact A22|].
  split. { intros x Hx. rewrite <- (KA x Hx). cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end; gres; reflexivity. }
  split; [eapply mem_grows_trans; [exact GF | exact GB]|].
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact AF | exact AB]|]. zsub. }
  assert (TB : forall a (k : nat) v, sp - 64 <= a -> a + Z.of_nat k <= sp -> cellA MF a k v -> cellA MB a k v).
  { intros a k v Ha Hk C. apply (art_cell_agree _ MF MB); [|lia|lia|exact C]. intros x Hx. unfold MB. apply art_rar_map_mem_agree; [lia|lia|lia]. }
  split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|]. split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|].
  split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|]. split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|].
  split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|]. split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|].
  split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|]. split; [apply TB; [lia|cbn; lia|unfold MF, art_pop_frame; zcell]|].
  rewrite A8 in F8. rewrite A9 in F9. rewrite A18 in F18, E18. rewrite A19 in E19. rewrite A20 in E20.
  rewrite art_u_lit in F8, F9, F18, E18, E19, E20 by lia.
  split; [exact F1|]. split; [exact F8|]. split; [exact F9|]. split; [exact F18|].
  split; [exact E1|]. split; [exact E8|]. split; [exact E9|]. split; [exact E18|]. split; [exact E19|]. exact E20.
Qed.

#[using="Type"] Lemma art_div8_lin : forall qs c km, (65536 * qs + c * 2 ^ 32 + 262144 * km) / 8 = 8192 * qs + c * 2 ^ 29 + 32768 * km.
Proof. intros. replace (65536 * qs + c * 2 ^ 32 + 262144 * km) with ((8192 * qs + c * 2 ^ 29 + 32768 * km) * 8) by lia. apply Z_div_mult. lia. Qed.
#[using="Type"] Lemma art_mod8_lin : forall qs c km, (65536 * qs + c * 2 ^ 32 + 262144 * km) mod 8 = 0.
Proof. intros. replace (65536 * qs + c * 2 ^ 32 + 262144 * km) with ((8192 * qs + c * 2 ^ 29 + 32768 * km) * 8) by lia. apply Z_mod_mult. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma art_clspop_B : forall regs (M rom : word -> option byte) (sp tp key tsd ctx t r c spb qs au mu km nf sz new rem m1 m2 sv addr shb : Z),
  addr = spb + c * 2 ^ 32 + mu -> shb = 2147450880 + 8192 * qs + c * 2 ^ 29 + 32768 * km ->
  getr regs 1 = Z_to_bv 64 0x8da40 -> getr regs 2 = Z_to_bv 64 (sp - 64 - 128) -> getr regs 4 = Z_to_bv 64 tp -> getr regs 8 = Z_to_bv 64 262144 ->
  getr regs 10 = Z_to_bv 64 addr -> getr regs 21 = Z_to_bv 64 sz -> getr regs 22 = Z_to_bv 64 1295832 ->
  0x696000 + 464 <= sp -> sp < 2 ^ 47 -> 1 <= c <= 30 -> spb = 65536 * qs -> mu = 262144 * km -> 0 <= km -> kHighMemBeg <= spb -> spb + 2 ^ 37 < 2 ^ 47 ->
  mu + 2 ^ 18 <= 3758096384 -> 32 <= sz <= 65536 -> 0 <= au -> au <= mu -> mu + 262144 - au = new * sz + rem -> 0 <= rem < sz -> 0 <= new -> 0 <= nf < 2 ^ 32 ->
  0 <= m1 < 2 ^ 64 -> 0 <= m2 < 2 ^ 64 -> 0 <= sv < 2 ^ 64 ->
  4096 <= t -> t + 4096 <= sp - 464 -> (t + 2792) mod 8 = 0 -> 0x696000 <= r -> r + 128 <= sp - 464 -> apart t 4096 r 128 ->
  0x10100 <= tp -> tp + 8 <= 0x696000 -> 0x10000 <= tsd -> tsd + 1024 <= 0x696000 -> 4096 <= ctx -> ctx + 4096 <= sp - 464 ->
  apart shb 32768 t 4096 -> apart shb 32768 r 128 -> apart shb 32768 ctx 4096 -> shb + 32768 <= sp - 464 ->
  wrA M (sp - 464) 400 -> wrA M shb 32768 -> wrA M (t + 2872) 16 -> wrA M (t + 2792) 8 -> wrA M r 128 ->
  art_layout M -> art_tsd M tp key tsd ctx t ->
  cellA M (sp - 64 - 8) 8 0x579b4 -> cellA M (sp - 64 - 16) 8 r -> cellA M (sp - 64 - 24) 8 (t + 2768) -> cellA M (sp - 64 - 32) 8 (spb + c * 2 ^ 32) ->
  cellA M (sp - 64 - 40) 8 0x95bf8 -> cellA M (sp - 64 - 48) 8 262144 -> cellA M (sp - 64 - 56) 8 addr ->
  cellA M (sp - 64 - 64) 8 (spb + c * 2 ^ 32) -> cellA M (sp - 64 - 72) 8 262144 -> cellA M (sp - 64 - 80) 8 addr ->
  cellA M 0x1374b0 8 0x1d1768 -> cellA M (0x1d1768 + 144) 8 0 ->
  cellA M (t + 2872) 8 m1 -> cellA M (t + 2880) 8 m2 -> cellA M (t + 2792) 8 sv -> cellA M (r + 48) 8 mu -> cellA M (r + 32) 8 au -> cellA M (r + 16) 8 nf ->
  exists regs' M',
    msteps ASEGS (mkst regs (0x8bc84 : word) M rom) (mkst regs' (0x55558 : word) M' rom)
    /\ getr regs' 1 = (0x57a28 : bv 64)%bv /\ getr regs' 2 = Z_to_bv 64 (sp - 64) /\ getr regs' 4 = Z_to_bv 64 tp /\ getr regs' 8 = Z_to_bv 64 r
    /\ getr regs' 9 = Z_to_bv 64 (nf + new) /\ getr regs' 10 = Z_to_bv 64 1295832 /\ getr regs' 11 = Z_to_bv 64 r /\ getr regs' 12 = Z_to_bv 64 (spb + c * 2 ^ 32)
    /\ getr regs' 13 = Z_to_bv 64 (nf + new) /\ getr regs' 18 = Z_to_bv 64 (spb + c * 2 ^ 32) /\ getr regs' 19 = Z_to_bv 64 new
    /\ getr regs' 20 = Z_to_bv 64 (mu + 262144 - au) /\ getr regs' 21 = Z_to_bv 64 sz /\ getr regs' 22 = Z_to_bv 64 1295832
    /\ (forall x : reg, In x [3; 23; 24; 25; 26; 27]%bv -> getr regs' x = getr regs x)
    /\ mem_grows M M' /\ art_agree [(sp - 464, 400); (shb, 32768); (t + 2872, 16); (t + 2792, 8); (r + 48, 8)] M M'
    /\ (forall j, 0 <= j < 32768 -> cellA M' (shb + j) 1 250)
    /\ cellA M' (t + 2872) 8 (m1 + 1) /\ cellA M' (t + 2880) 8 (m2 + 262144) /\ cellA M' (t + 2792) 8 (sv + 262144) /\ cellA M' (r + 48) 8 (mu + 262144).
Proof.
  intros regs M rom sp tp key tsd ctx t r c spb qs au mu km nf sz new rem m1 m2 sv addr shb Haddr Hshb H1 H2 H4 H8 H10 H21 H22 IMG Hsp' Hc Espb Emu Hkm Hspb Hspb' Hex Hsz Hau Haumu Enew Hrem Hnew Hnf
         Hm1 Hm2 Hsv Ht Ht' Hst8 Hr Hr' Atr Htp Htp' Htsd Htsd' Hctx Hctx' Ast Asr Asc Hshsp W Wsh Wts Wsv Wr L T F1 F8 F9 F18 E1 E8 E9 E18 E19 E20 Ccf Clim Cm1 Cm2 Csv Cmu Cau Cnf.
  unfold kHighMemBeg in Hspb.
  assert (Eshb : SB + addr / 8 = shb). { rewrite Haddr, Hshb. unfold SB. rewrite Espb, Emu, art_div8_lin. lia. }
  (* [comment removed for export] *)
  pose proof (art_rar_map_post_fn regs M rom (0x579b4 : bv 64)%bv (Z_to_bv 64 r) (Z_to_bv 64 (t + 2768)) (Z_to_bv 64 (spb + c * 2 ^ 32)) (Z_to_bv 64 262144) (Z_to_bv 64 addr)
                (Z_to_bv 64 262144) (Z_to_bv 64 addr) (Z_to_bv 64 (spb + c * 2 ^ 32))
                (sp - 64) 262144 addr 0x1d1768 H1 H2 H8 H10 ltac:(unfold ret_ok; bveq) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
                ltac:(eapply wr_sub; [exact W|lia|lia])
                ltac:(exact F1) ltac:(rewrite art_u_lit by lia; exact F8) ltac:(rewrite art_u_lit by lia; exact F9) ltac:(rewrite art_u_lit by lia; exact F18)
                ltac:(exact E1) ltac:(rewrite art_u_lit by lia; exact E8) ltac:(rewrite art_u_lit by lia; exact E9)
                ltac:(rewrite art_u_lit by lia; exact E18) ltac:(rewrite art_u_lit by lia; exact E19) ltac:(rewrite art_u_lit by lia; exact E20)
                Ccf Clim) as RUN1.      (* [comment removed for export] *)
  match type of RUN1 with msteps _ _ (mkst ?R _ ?MM _) => set (r1 := R) in RUN1; set (M1 := MM) in RUN1 end.
  assert (A1 : art_agree [(sp - 464, 400)] M M1). { eapply art_agree_sub; [unfold M1; zagree|]. zsub. }
  assert (G1 : mem_grows M M1) by (unfold M1; zgrows).
  (* [comment removed for export] *)
  pose proof (art_pop_b_fn r1 M1 rom addr ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(unfold r1; gres; reflexivity) ltac:(lia)) as RUN2.
  match type of RUN2 with msteps _ _ (mkst ?R _ _ _) => set (r2 := R) in RUN2 end.
  (* [comment removed for export] *)
  assert (L1 : art_layout M1). { eapply art_layout_fp; [exact A1| |exact L]. intros z Hz. cbn. repeat split; lia. }
  destruct (art_poison_hi_run r2 M1 rom (0x579d0 : bv 64)%bv (sp - 64) addr 262144 250
              ltac:(unfold r2; gres; reflexivity) ltac:(unfold ret_ok; bveq) ltac:(unfold r2, r1; gres; reflexivity) ltac:(unfold r2; gres; reflexivity)
              ltac:(unfold r2; gres; reflexivity) ltac:(unfold r2; gres; reflexivity)
              ltac:(lia) ltac:(lia) ltac:(eapply wr_grows; [exact G1|]; eapply wr_sub; [exact W|lia|lia]) ltac:(unfold apart; lia) ltac:(unfold apart; lia)
              L1 ltac:(unfold kHighMemBeg; lia) ltac:(unfold kHighMemEnd; lia)
              ltac:(rewrite Haddr, Espb, Emu; apply art_mod8_lin) ltac:(reflexivity) ltac:(lia) ltac:(lia) ltac:(intros E; discriminate E)
              ltac:(rewrite Eshb; change (262144 / 8) with 32768; eapply wr_grows; [exact G1|exact Wsh]))
    as (r3 & RUN3 & P10 & P1 & P2 & P8 & P9 & P18 & P19 & P20 & P21 & KP).
  match type of RUN3 with msteps _ _ (mkst _ _ ?MM _) => set (M3 := MM) in RUN3 end.
  assert (A3 : art_agree [(sp - 464, 400); (shb, 32768)] M1 M3).
  { unfold M3, art_poison_frame. rewrite Eshb. change (262144 / 8) with 32768. eapply art_agree_sub; [zagree|]. rewrite Z2Nat.id by lia. zsub. }
  assert (G3 : mem_grows M1 M3) by (unfold M3, art_poison_frame; zgrows).
  assert (A13 : art_agree [(sp - 464, 400); (shb, 32768)] M M3). { eapply art_agree_sub; [eapply art_agree_trans; [exact A1|exact A3]|]. zsub. }
  assert (G13 : mem_grows M M3) by (eapply mem_grows_trans; eassumption).
  assert (Hqs : 0 <= qs) by lia.
  assert (T3 : art_tsd M3 tp key tsd ctx t).
  { eapply art_tsd_fp; [exact A13| | |exact Htp|exact Htp'|exact Htsd|exact Htsd'|exact T].
    - intros z Hz. cbn. repeat split; lia.
    - intros z Hz. cbn. unfold apart in Asc. repeat split; lia. }
  assert (R3_4 : getr r3 4 = Z_to_bv 64 tp). { rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E). unfold r2, r1; gres. exact H4. }
  assert (R3_22 : getr r3 22 = Z_to_bv 64 1295832). { rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E). unfold r2, r1; gres. exact H22. }
  assert (R3_8 : getr r3 8 = Z_to_bv 64 r). { rewrite P8. unfold r2, r1; gres. reflexivity. }
  assert (R3_9 : getr r3 9 = Z_to_bv 64 (t + 2768)). { rewrite P9. unfold r2, r1; gres. reflexivity. }
  assert (R3_18 : getr r3 18 = Z_to_bv 64 (spb + c * 2 ^ 32)). { rewrite P18. unfold r2, r1; gres. reflexivity. }
  assert (R3_19 : getr r3 19 = Z_to_bv 64 262144). { rewrite P19. unfold r2, r1; gres. reflexivity. }
  assert (R3_21 : getr r3 21 = Z_to_bv 64 sz). { rewrite P21. unfold r2, r1; gres. exact H21. }
  pose proof (art_pop_c_fn r3 M3 rom (sp - 64) tp key tsd ctx t 1295832 (t + 2768) r (spb + c * 2 ^ 32) sz au mu nf new rem m1 m2 sv
                P2 R3_4 R3_8 R3_9 R3_18 R3_19 R3_21 R3_22
                ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(replace (t + 2768 + 24) with (t + 2792) by lia; exact Hst8) ltac:(lia) ltac:(lia) ltac:(lia)
                Hsz Hau Haumu ltac:(lia) Enew Hrem Hnew Hnf Hm1 Hm2 Hsv ltac:(lia) ltac:(lia)
                ltac:(eapply wr_grows; [exact G13|]; eapply wr_sub; [exact W|lia|lia]) T3
                ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; destruct T as (_ & _ & _ & _ & _ & _ & _ & Hk & _); lia) ltac:(unfold apart; lia)
                ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart; lia) ltac:(unfold apart in Atr |- *; lia) ltac:(unfold apart in Atr |- *; lia)
                ltac:(eapply wr_grows; [exact G13|exact Wts]) ltac:(eapply wr_grows; [exact G13|]; replace (t + 2768 + 24) with (t + 2792) by lia; exact Wsv) ltac:(eapply wr_grows; [exact G13|exact Wr])
                ltac:(unfold apart in Ast; ztr) ltac:(unfold apart in Ast; ztr) ltac:(replace (t + 2768 + 24) with (t + 2792) by lia; unfold apart in Ast; ztr)
                ltac:(unfold apart in Asr; ztr) ltac:(unfold apart in Asr; ztr) ltac:(unfold apart in Asr; ztr)) as RUN4.
  match type of RUN4 with msteps _ _ (mkst ?R _ ?MM _) => set (r4 := R) in RUN4; set (M4 := MM) in RUN4 end.
  assert (A4 : art_agree [(sp - 464, 400); (t + 2872, 16); (t + 2792, 8); (r + 48, 8)] M3 M4).
  { unfold M4, art_pop_c_mem. eapply art_agree_sub; [zagree|]. zsub. }
  assert (G4 : mem_grows M3 M4) by (unfold M4, art_pop_c_mem; zgrows).
  exists r4, M4. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3|exact RUN4]|].
  split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; exact R3_4|]. split; [unfold r4; gres; exact R3_8|].
  split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|].
  split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; exact R3_18|]. split; [unfold r4; gres; reflexivity|]. split; [unfold r4; gres; reflexivity|].
  split; [unfold r4; gres; exact R3_21|]. split; [unfold r4; gres; exact R3_22|].
  split. { intros x Hx. cbn [In] in Hx. repeat match type of Hx with _ \/ _ => destruct Hx as [<-|Hx] | False => destruct Hx end;
           (unfold r4; gres; rewrite KP by (unfold art_poison_kept; repeat split; intros E; discriminate E); unfold r2, r1; gres; reflexivity). }
  split; [eapply mem_grows_trans; [exact G13|exact G4]|].
  split. { eapply art_agree_sub; [eapply art_agree_trans; [exact A13|exact A4]|]. zsub. }
  split. { intros j Hj. assert (C3 : cellA M3 (shb + j) 1 250).
           { unfold M3. rewrite Eshb. apply cell_Wf_in; [lia|change (262144 / 8) with 32768; rewrite Z2Nat.id by lia; lia|change (262144 / 8) with 32768; rewrite Z2Nat.id by lia; lia|lia]. }
           unfold apart in Ast, Asr. ztr. }
  unfold M4, art_pop_c_mem. unfold apart in Atr.
  split; [zcell|]. split; [zcell|]. split; [replace (t + 2792) with (t + 2768 + 24) by lia; zcell|]. zcell.
Qed.
End FPX.
