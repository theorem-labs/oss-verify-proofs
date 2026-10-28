(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.leptonica.grayquant_fuzzer.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk StartupTac.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib W2Lib LeptStructs LeptExec DitherLib DitherTac DitherLib2 DitherTac2 DitherTab.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.leptonica.grayquant_fuzzer.lib.Common Require LiaFast.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ solve [LiaFast.flia2] | Zify.zify; xlia zchecker ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Local Abbreviation SEGS := Ubsan.M.loaded_segments.

Lemma wr_readable_img : wr_readable SEGS.
Proof.
  intros seg Hin Hwr. cbn in Hin.
  repeat (destruct Hin as [<-|Hin]; [first [reflexivity | discriminate Hwr] |]). destruct Hin.
Qed.

Definition v0_1eddc_cells_def (lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld : Z) : list (Z * Z) := [((bytea (bufs1 + j))%Z, 1%Z); ((lined + (4 * (j / 16)))%Z, 4%Z); ((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)].
(* [comment removed for export] *)
Definition v0_hyps (lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (4096 <= tab14 <= 140737488355328)%Z /\ (tab14 mod 4 = 0)%Z /\ (0 <= j <= 19999)%Z /\ (1 <= w1 <= 19999)%Z /\ (0 <= j < w1)%Z /\ (w1 + 1 <= 4 * wpl)%Z /\ (w1 + 1 <= 16 * wpld)%Z /\ dapart lined (4 * wpld) bufs1 (4 * wpl) /\ dapart lined (4 * wpld) bufs2 (4 * wpl) /\ dapart lined (4 * wpld) tab38 1024 /\ dapart lined (4 * wpld) tab14 1024.
Section V0.
Variable rom : word -> option byte.
Variables (lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld : Z).
Hypothesis HYP : v0_hyps lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_tabval & A_tabval & R_tab38 & A_tab38 & R_tab14 & A_tab14 & R_j & R_w1 & Hj & Hwpl & Hwpld & AP_l1 & AP_l2 & AP_l38 & AP_l14); pose proof (dl_div_bounds j 16 ltac:(lia) ltac:(lia)) as DJ; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1]; destruct (al4_ex _ A_bufs2) as [cb2 Ecb2].
(* [comment removed for export] *)
Lemma v0_1edd8f : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 w1) (Z_to_bv 64 (j + 1)) = false ->
  getr regs 5 = Z_to_bv 64 (j + 1) ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1eedc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1eee0) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H28 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1edd8t : forall (fx : FPState) regs m ,
  branch_taken BC_EQ (Z_to_bv 64 w1) (Z_to_bv 64 (j + 1)) = true ->
  getr regs 5 = Z_to_bv 64 (j + 1) ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1eedc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f048) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H28 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1eddc : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte) (bs5 : list byte) (bs6 : list byte) (bs7 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (j / 16)))) 4 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (tabval + (4 * (rdv false 1 bs0)))) 4 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (tab38 + (4 * (rdv false 1 bs0)))) 4 = Some bs3 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = Some bs4 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = Some bs5 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = Some bs6 ->
  rdn SEGS m (Z_to_bv 64 (tab14 + (4 * (rdv false 1 bs0)))) 4 = Some bs7 ->
  tv_ok (rdv true 4 bs3) ->
  tv_ok (rdv true 4 bs7) ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (j / 16)))) 4 = true ->
  getr regs 5 = Z_to_bv 64 j ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1eee0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1eff0) m' rom)
    /\ mframe [((lined + (4 * (j / 16)))%Z, 4%Z)] m m'
    /\ getr regs' 9 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ getr regs' 18 = Z_to_bv 64 (bytea (bufs2 + j))
    /\ getr regs' 19 = Z_to_bv 64 (bytea (bufs2 + j + 1))
    /\ getr regs' 20 = Z_to_bv 64 (rdv false 1 bs4)
    /\ getr regs' 21 = Z_to_bv 64 (rdv true 4 bs3)
    /\ getr regs' 22 = Z_to_bv 64 (rdv false 1 bs5)
    /\ getr regs' 23 = Z_to_bv 64 (rdv true 4 bs7)
    /\ getr regs' 24 = Z_to_bv 64 (rdv false 1 bs6)
    /\ regs_agree (fun r => In r [9; 18; 19; 20; 21; 22; 23; 24]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 bs5 bs6 bs7 R0 R1 R2 R3 R4 R5 R6 R7 TV3 TV7 S0 H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H28 H31.
  dl_facts.
  pose proof (tv_range _ TV3) as RGT3.
  pose proof (tv_range _ TV7) as RGT7.
  pose proof (rdv_u8 SEGS _ _ _ R0) as U0.
  pose proof (rdv_u8 SEGS _ _ _ R4) as U4.
  pose proof (rdv_u8 SEGS _ _ _ R5) as U5.
  pose proof (rdv_u8 SEGS _ _ _ R6) as U6.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv true 4 bs3; rdv false 1 bs4; rdv false 1 bs5; rdv false 1 bs6; rdv true 4 bs7] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv true 4 bs3; rdv false 1 bs4; rdv false 1 bs5; rdv false 1 bs6; rdv true 4 bs7]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [false; false; false; false; false; false; false] [EVar 40; EVar 41; EVar 42; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1eeecf : forall (fx : FPState) regs m  (d20 d21 d22 d23 d24 : Z),
  branch_taken BC_LT (Z_to_bv 64 d21) (Z_to_bv 64 0) = false ->
  getr regs 5 = Z_to_bv 64 j ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 18 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 20 = Z_to_bv 64 d20 ->
  getr regs 21 = Z_to_bv 64 d21 ->
  getr regs 22 = Z_to_bv 64 d22 ->
  getr regs 23 = Z_to_bv 64 d23 ->
  getr regs 24 = Z_to_bv 64 d24 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  (0 <= d20 <= 255)%Z ->
  tv_ok d21 ->
  (0 <= d22 <= 255)%Z ->
  tv_ok d23 ->
  (0 <= d24 <= 255)%Z ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1eff0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f008) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 25 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [20; 25]%list) regs regs'.
Proof using All.
  intros fx regs m d20 d21 d22 d23 d24 BT H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19 H20 H21 H22 H23 H24 H28 H31 DC20 DC21 DC22 DC23 DC24.
  dl_facts.
  pose proof (tv_range _ DC21) as RG21.
  pose proof (tv_nn30 _ DC21 BT) as NN21.
  pose proof (tv_range _ DC23) as RG23.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d20; d21; d22; d23; d24] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d20; d21; d22; d23; d24]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 56) 0 255; KRange (EVar 58) 0 255; KRange (EVar 60) 0 255]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1eeect : forall (fx : FPState) regs m  (d20 d21 d22 d23 d24 : Z),
  branch_taken BC_LT (Z_to_bv 64 d21) (Z_to_bv 64 0) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 j ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 18 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 20 = Z_to_bv 64 d20 ->
  getr regs 21 = Z_to_bv 64 d21 ->
  getr regs 22 = Z_to_bv 64 d22 ->
  getr regs 23 = Z_to_bv 64 d23 ->
  getr regs 24 = Z_to_bv 64 d24 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  (0 <= d20 <= 255)%Z ->
  tv_ok d21 ->
  (0 <= d22 <= 255)%Z ->
  tv_ok d23 ->
  (0 <= d24 <= 255)%Z ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1eff0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1eedc) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 5 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [5; 17; 20; 21; 22; 23; 25]%list) regs regs'.
Proof using All.
  intros fx regs m d20 d21 d22 d23 d24 BT S0 S1 S2 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19 H20 H21 H22 H23 H24 H28 H31 DC20 DC21 DC22 DC23 DC24.
  dl_facts.
  pose proof (tv_range _ DC21) as RG21.
  pose proof (tv_range _ DC23) as RG23.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d20; d21; d22; d23; d24] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d20; d21; d22; d23; d24]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 56) 0 255; KRange (EVar 58) 0 255; KRange (EVar 60) 0 255]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [true; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1ef04f : forall (fx : FPState) regs m  (d21 d22 d23 d24 : Z),
  branch_taken BC_LT (getr regs 20) (Z_to_bv 64 255) = false ->
  getr regs 5 = Z_to_bv 64 j ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 18 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 21 = Z_to_bv 64 d21 ->
  getr regs 22 = Z_to_bv 64 d22 ->
  getr regs 23 = Z_to_bv 64 d23 ->
  getr regs 24 = Z_to_bv 64 d24 ->
  getr regs 25 = Z_to_bv 64 255 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  (0 <= d21 < 1073741824)%Z ->
  (0 <= d22 <= 255)%Z ->
  tv_ok d23 ->
  (0 <= d24 <= 255)%Z ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f008) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f030) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 20 = Z_to_bv 64 255
    /\ getr regs' 23 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [20; 21; 22; 23; 25]%list) regs regs'.
Proof using All.
  intros fx regs m d21 d22 d23 d24 BT H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19 H21 H22 H23 H24 H25 H28 H31 DC21 DC22 DC23 DC24.
  dl_facts.
  pose proof (tv_range _ DC23) as RG23.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d21; d22; d23; d24] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d21; d22; d23; d24]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 56) 0 1073741823; KRange (EVar 57) 0 255; KRange (EVar 59) 0 255]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [false; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1ef04t : forall (fx : FPState) regs m  (d21 d22 d23 d24 : Z),
  branch_taken BC_LT (getr regs 20) (Z_to_bv 64 255) = true ->
  getr regs 5 = Z_to_bv 64 j ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 18 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 21 = Z_to_bv 64 d21 ->
  getr regs 22 = Z_to_bv 64 d22 ->
  getr regs 23 = Z_to_bv 64 d23 ->
  getr regs 24 = Z_to_bv 64 d24 ->
  getr regs 25 = Z_to_bv 64 255 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  (0 <= d21 < 1073741824)%Z ->
  (0 <= d22 <= 255)%Z ->
  tv_ok d23 ->
  (0 <= d24 <= 255)%Z ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f008) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f030) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 23 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [21; 22; 23; 25]%list) regs regs'.
Proof using All.
  intros fx regs m d21 d22 d23 d24 BT H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19 H21 H22 H23 H24 H25 H28 H31 DC21 DC22 DC23 DC24.
  dl_facts.
  pose proof (tv_range _ DC23) as RG23.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d21; d22; d23; d24] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d21; d22; d23; d24]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999; KRange (EVar 56) 0 1073741823; KRange (EVar 57) 0 255; KRange (EVar 59) 0 255]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [true; false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1ef2cf : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 21) (Z_to_bv 64 255) = false ->
  getr regs 5 = Z_to_bv 64 j ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 18 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 23 = Z_to_bv 64 255 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f030) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f03c) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 21 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [21; 22]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19 H23 H28 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1ef2ct : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 21) (Z_to_bv 64 255) = true ->
  getr regs 5 = Z_to_bv 64 j ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 18 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 23 = Z_to_bv 64 255 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f030) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f03c) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r [22]%list) regs regs'.
Proof using All.
  intros fx regs m  BT H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19 H23 H28 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1ef38f : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 22) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 j ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 18 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 23 = Z_to_bv 64 255 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f03c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1eedc) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 5 = Z_to_bv 64 (j + 1)
    /\ getr regs' 22 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [5; 17; 22]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19 H23 H28 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma v0_1ef38t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 22) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs1 + j + 1))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j))) 1 = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + j + 1))) 1 = true ->
  getr regs 5 = Z_to_bv 64 j ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 (bytea (bufs1 + j + 1)) ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 18 = Z_to_bv 64 (bytea (bufs2 + j)) ->
  getr regs 19 = Z_to_bv 64 (bytea (bufs2 + j + 1)) ->
  getr regs 23 = Z_to_bv 64 255 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f03c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1eedc) m' rom)
    /\ mframe [((bytea (bufs1 + j + 1))%Z, 1%Z); ((bytea (bufs2 + j))%Z, 1%Z); ((bytea (bufs2 + j + 1))%Z, 1%Z)] m m'
    /\ getr regs' 5 = Z_to_bv 64 (j + 1)
    /\ regs_agree (fun r => In r [5; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 S1 S2 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H18 H19 H23 H28 H31.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; tab14; j; w1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 0 19999; KRange (EVar 39) 1 19999]) by (ex_know regs).
  dl_run 400%nat [126684%Z; 126688%Z; 127048%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation v0_1eddc_cells := (v0_1eddc_cells_def lined bufs1 bufs2 tabval tab38 tab14 j w1 wpl wpld).
Lemma v0_1eddc_path : forall (fx : FPState) regs m,
  cells_ok SEGS m v0_1eddc_cells ->
  tab_rd SEGS false (fun _ => True) v0_1eddc_cells m tabval ->
  tab_rd SEGS true tv_ok v0_1eddc_cells m tab38 ->
  tab_rd SEGS true tv_ok v0_1eddc_cells m tab14 ->
  getr regs 5 = Z_to_bv 64 j ->
  getr regs 6 = Z_to_bv 64 3 ->
  getr regs 7 = Z_to_bv 64 1 ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w1 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  getr regs 16 = Z_to_bv 64 tab14 ->
  getr regs 28 = Z_to_bv 64 1 ->
  getr regs 31 = Z_to_bv 64 268435455 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1eee0) m rom) (@mkst fx regs' (Z_to_bv 64 0x1eedc) m' rom)
    /\ mframe v0_1eddc_cells m m'
    /\ getr regs' 5 = Z_to_bv 64 (j + 1)
    /\ getr regs' 9 = Z_to_bv 64 (bytea (bufs1 + j + 1))
    /\ getr regs' 18 = Z_to_bv 64 (bytea (bufs2 + j))
    /\ getr regs' 19 = Z_to_bv 64 (bytea (bufs2 + j + 1))
    /\ regs_agree (fun r => In r [5; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25]%list) regs regs'.
Proof using All.
  intros fx regs m CK TR_tabval_false TR_tab38_true TR_tab14_true H5 H6 H7 H8 H10 H11 H12 H13 H14 H15 H16 H28 H31.
  pose proof (mframe_refl v0_1eddc_cells m) as FK0.
  destruct (cells_ok_read SEGS m m v0_1eddc_cells (bytea (bufs1 + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (cells_ok_read SEGS m m v0_1eddc_cells (lined + (4 * (j / 16)))%Z 4%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_1 Rd1_1].
  destruct (TR_tabval_false m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_2 & Rd1_2 & TV1_2).
  destruct (TR_tab38_true m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_3 & Rd1_3 & TV1_3).
  destruct (cells_ok_read SEGS m m v0_1eddc_cells (bytea (bufs1 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_4 Rd1_4].
  destruct (cells_ok_read SEGS m m v0_1eddc_cells (bytea (bufs2 + j))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_5 Rd1_5].
  destruct (cells_ok_read SEGS m m v0_1eddc_cells (bytea (bufs2 + j + 1))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_6 Rd1_6].
  destruct (TR_tab14_true m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_7 & Rd1_7 & TV1_7).
  destruct (v0_1eddc fx regs m bs1_0 bs1_1 bs1_2 bs1_3 bs1_4 bs1_5 bs1_6 bs1_7 Rd1_0 Rd1_1 Rd1_2 Rd1_3 Rd1_4 Rd1_5 Rd1_6 Rd1_7 TV1_3 TV1_7 (cells_ok_sok SEGS m m v0_1eddc_cells (lined + (4 * (j / 16)))%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_9 & E1_18 & E1_19 & E1_20 & E1_21 & E1_22 & E1_23 & E1_24 & AG1).
  assert (FK1 : mframe v0_1eddc_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold v0_1eddc_cells_def; dl_incl).
  assert (DX : exists d, getr r1 20 = Z_to_bv 64 d /\ (0 <= d <= 255)%Z) by (eexists; split; [dl_get | dl_dclass]).
  destruct DX as (d2_20 & DE2_20 & DC2_20).
  assert (DX : exists d, getr r1 21 = Z_to_bv 64 d /\ tv_ok d) by (eexists; split; [dl_get | dl_dclass]).
  destruct DX as (d2_21 & DE2_21 & DC2_21).
  assert (DX : exists d, getr r1 22 = Z_to_bv 64 d /\ (0 <= d <= 255)%Z) by (eexists; split; [dl_get | dl_dclass]).
  destruct DX as (d2_22 & DE2_22 & DC2_22).
  assert (DX : exists d, getr r1 23 = Z_to_bv 64 d /\ tv_ok d) by (eexists; split; [dl_get | dl_dclass]).
  destruct DX as (d2_23 & DE2_23 & DC2_23).
  assert (DX : exists d, getr r1 24 = Z_to_bv 64 d /\ (0 <= d <= 255)%Z) by (eexists; split; [dl_get | dl_dclass]).
  destruct DX as (d2_24 & DE2_24 & DC2_24).
  destruct (branch_taken BC_LT (Z_to_bv 64 d2_21) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (v0_1eeect fx r1 m1 d2_20 d2_21 d2_22 d2_23 d2_24 B1 (cells_ok_sok SEGS m m1 v0_1eddc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK1) ltac:(dl_in0)) (cells_ok_sok SEGS m m1 v0_1eddc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK1) ltac:(dl_in0)) (cells_ok_sok SEGS m m1 v0_1eddc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) DC2_20 DC2_21 DC2_22 DC2_23 DC2_24) as (r2 & m2 & RUN2 & FR2 & E2_5 & AG2).
    assert (FK2 : mframe v0_1eddc_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold v0_1eddc_cells_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (v0_1eeecf fx r1 m1 d2_20 d2_21 d2_22 d2_23 d2_24 B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) DC2_20 DC2_21 DC2_22 DC2_23 DC2_24) as (r2 & m2 & RUN2 & FR2 & E2_25 & AG2).
    assert (FK2 : mframe v0_1eddc_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold v0_1eddc_cells_def; dl_incl).
    assert (DX : exists d, getr r2 21 = Z_to_bv 64 d /\ (0 <= d < 1073741824)%Z) by (eexists; split; [dl_get | dl_dclass]).
    destruct DX as (d3_21 & DE3_21 & DC3_21).
    assert (DX : exists d, getr r2 22 = Z_to_bv 64 d /\ (0 <= d <= 255)%Z) by (eexists; split; [dl_get | dl_dclass]).
    destruct DX as (d3_22 & DE3_22 & DC3_22).
    assert (DX : exists d, getr r2 23 = Z_to_bv 64 d /\ tv_ok d) by (eexists; split; [dl_get | dl_dclass]).
    destruct DX as (d3_23 & DE3_23 & DC3_23).
    assert (DX : exists d, getr r2 24 = Z_to_bv 64 d /\ (0 <= d <= 255)%Z) by (eexists; split; [dl_get | dl_dclass]).
    destruct DX as (d3_24 & DE3_24 & DC3_24).
    destruct (branch_taken BC_LT (getr r2 20) (Z_to_bv 64 255)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (v0_1ef04t fx r2 m2 d3_21 d3_22 d3_23 d3_24 B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) DC3_21 DC3_22 DC3_23 DC3_24) as (r3 & m3 & RUN3 & FR3 & E3_23 & AG3).
      assert (FK3 : mframe v0_1eddc_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v0_1eddc_cells_def; dl_incl).
      destruct (branch_taken BC_LT (getr r3 21) (Z_to_bv 64 255)) eqn:B3.
      * (* [comment removed for export] *)
        destruct (v0_1ef2ct fx r3 m3  B3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & AG4).
        assert (FK4 : mframe v0_1eddc_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold v0_1eddc_cells_def; dl_incl).
        destruct (branch_taken BC_LT (getr r4 22) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (v0_1ef38t fx r4 m4  B4 (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_5 & AG5).
          assert (FK5 : mframe v0_1eddc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1eddc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (v0_1ef38f fx r4 m4  B4 (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_5 & E5_22 & AG5).
          assert (FK5 : mframe v0_1eddc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1eddc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (v0_1ef2cf fx r3 m3  B3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_21 & AG4).
        assert (FK4 : mframe v0_1eddc_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold v0_1eddc_cells_def; dl_incl).
        destruct (branch_taken BC_LT (getr r4 22) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (v0_1ef38t fx r4 m4  B4 (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_5 & AG5).
          assert (FK5 : mframe v0_1eddc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1eddc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (v0_1ef38f fx r4 m4  B4 (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_5 & E5_22 & AG5).
          assert (FK5 : mframe v0_1eddc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1eddc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (v0_1ef04f fx r2 m2 d3_21 d3_22 d3_23 d3_24 B2 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) DC3_21 DC3_22 DC3_23 DC3_24) as (r3 & m3 & RUN3 & FR3 & E3_20 & E3_23 & AG3).
      assert (FK3 : mframe v0_1eddc_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold v0_1eddc_cells_def; dl_incl).
      destruct (branch_taken BC_LT (getr r3 21) (Z_to_bv 64 255)) eqn:B3.
      * (* [comment removed for export] *)
        destruct (v0_1ef2ct fx r3 m3  B3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & AG4).
        assert (FK4 : mframe v0_1eddc_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold v0_1eddc_cells_def; dl_incl).
        destruct (branch_taken BC_LT (getr r4 22) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (v0_1ef38t fx r4 m4  B4 (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_5 & AG5).
          assert (FK5 : mframe v0_1eddc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1eddc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (v0_1ef38f fx r4 m4  B4 (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_5 & E5_22 & AG5).
          assert (FK5 : mframe v0_1eddc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1eddc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
      * (* [comment removed for export] *)
        destruct (v0_1ef2cf fx r3 m3  B3 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r4 & m4 & RUN4 & FR4 & E4_21 & AG4).
        assert (FK4 : mframe v0_1eddc_cells m m4) by (apply (mframe_step _ _ _ _ _ FK3 FR4); unfold v0_1eddc_cells_def; dl_incl).
        destruct (branch_taken BC_LT (getr r4 22) (Z_to_bv 64 255)) eqn:B4.
        -- (* [comment removed for export] *)
          destruct (v0_1ef38t fx r4 m4  B4 (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_5 & AG5).
          assert (FK5 : mframe v0_1eddc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1eddc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
        -- (* [comment removed for export] *)
          destruct (v0_1ef38f fx r4 m4  B4 (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs1 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) (cells_ok_sok SEGS m m4 v0_1eddc_cells (bytea (bufs2 + j + 1))%Z 1%Z CK (proj1 FK4) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r5 & m5 & RUN5 & FR5 & E5_5 & E5_22 & AG5).
          assert (FK5 : mframe v0_1eddc_cells m m5) by (apply (mframe_step _ _ _ _ _ FK4 FR5); unfold v0_1eddc_cells_def; dl_incl).
          exists r5, m5. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 (msteps_trans _ _ _ _ RUN3 (msteps_trans _ _ _ _ RUN4 RUN5))))|]. split; [exact FK5|].
          repeat split; [dl_get .. | ra_chain].
Qed.

End V0.

Definition vt0_1ef44_cells_def (lined bufs1 bufs2 tabval tab38 w0 wpl wpld : Z) : list (Z * Z) := [((bytea (bufs1 + w0))%Z, 1%Z); ((lined + (4 * (w0 / 16)))%Z, 4%Z); ((bytea (bufs2 + w0))%Z, 1%Z)].
(* [comment removed for export] *)
Definition vt0_hyps (lined bufs1 bufs2 tabval tab38 w0 wpl wpld : Z) : Prop :=
  (4096 <= lined <= 140737488355328)%Z /\ (lined mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (0 <= w0 <= 19999)%Z /\ (w0 + 1 <= 4 * wpl)%Z /\ (w0 + 1 <= 16 * wpld)%Z /\ dapart lined (4 * wpld) bufs2 (4 * wpl) /\ dapart lined (4 * wpld) tab38 1024.
Section VT0.
Variable rom : word -> option byte.
Variables (lined bufs1 bufs2 tabval tab38 w0 wpl wpld : Z).
Hypothesis HYP : vt0_hyps lined bufs1 bufs2 tabval tab38 w0 wpl wpld.
Ltac dl_facts := pose proof HYP as (R_lined & A_lined & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_tabval & A_tabval & R_tab38 & A_tab38 & R_w0 & Hwpl & Hwpld & AP_l2 & AP_l38); pose proof (dl_div_bounds w0 16 ltac:(lia) ltac:(lia)) as DW; destruct (al4_ex _ A_bufs1) as [cb1 Ecb1]; destruct (al4_ex _ A_bufs2) as [cb2 Ecb2].
(* [comment removed for export] *)
Lemma vt0_1ef44 : forall (fx : FPState) regs m (bs0 : list byte) (bs1 : list byte) (bs2 : list byte) (bs3 : list byte) (bs4 : list byte),
  rdn SEGS m (Z_to_bv 64 (bytea (bufs1 + w0))) 1 = Some bs0 ->
  rdn SEGS m (Z_to_bv 64 (lined + (4 * (w0 / 16)))) 4 = Some bs1 ->
  rdn SEGS m (Z_to_bv 64 (tabval + (4 * (rdv false 1 bs0)))) 4 = Some bs2 ->
  rdn SEGS m (Z_to_bv 64 (tab38 + (4 * (rdv false 1 bs0)))) 4 = Some bs3 ->
  rdn SEGS m (Z_to_bv 64 (bytea (bufs2 + w0))) 1 = Some bs4 ->
  tv_ok (rdv true 4 bs3) ->
  store_ok SEGS m (Z_to_bv 64 (lined + (4 * (w0 / 16)))) 4 = true ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w0 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f048) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f134) m' rom)
    /\ mframe [((lined + (4 * (w0 / 16)))%Z, 4%Z)] m m'
    /\ getr regs' 7 = Z_to_bv 64 30
    /\ getr regs' 10 = Z_to_bv 64 (bytea (bufs2 + w0))
    /\ getr regs' 11 = Z_to_bv 64 (rdv true 4 bs3)
    /\ getr regs' 12 = Z_to_bv 64 (rdv false 1 bs4)
    /\ regs_agree (fun r => In r [5; 6; 7; 10; 11; 12; 13; 14; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m bs0 bs1 bs2 bs3 bs4 R0 R1 R2 R3 R4 TV3 S0 H10 H11 H12 H13 H14 H15.
  dl_facts.
  pose proof (tv_range _ TV3) as RGT3.
  pose proof (rdv_u8 SEGS _ _ _ R0) as U0.
  pose proof (rdv_u8 SEGS _ _ _ R4) as U4.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; w0; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv true 4 bs3; rdv false 1 bs4] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; w0; rdv false 1 bs0; rdv true 4 bs1; rdv false 4 bs2; rdv true 4 bs3; rdv false 1 bs4]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 0 19999]) by (ex_know regs).
  dl_run 400%nat [127340%Z] (SCR [false; false; false; false; false; false; false; false] [EVar 38; EVar 39; EVar 40; EVar 41; EVar 42] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1f030f : forall (fx : FPState) regs m  (d11 d12 : Z),
  branch_taken BC_LT (Z_to_bv 64 d11) (Z_to_bv 64 0) = false ->
  getr regs 7 = Z_to_bv 64 30 ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w0)) ->
  getr regs 11 = Z_to_bv 64 d11 ->
  getr regs 12 = Z_to_bv 64 d12 ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  tv_ok d11 ->
  (0 <= d12 <= 255)%Z ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f134) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f14c) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 12 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [11; 12; 13]%list) regs regs'.
Proof using All.
  intros fx regs m d11 d12 BT H7 H10 H11 H12 H15 DC11 DC12.
  dl_facts.
  pose proof (tv_range _ DC11) as RG11.
  pose proof (tv_nn30 _ DC11 BT) as NN11.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; w0; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d11; d12] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; w0; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d11; d12]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 0 19999; KRange (EVar 57) 0 255]) by (ex_know regs).
  dl_run 400%nat [127340%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1f030t : forall (fx : FPState) regs m  (d11 d12 : Z),
  branch_taken BC_LT (Z_to_bv 64 d11) (Z_to_bv 64 0) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w0))) 1 = true ->
  getr regs 7 = Z_to_bv 64 30 ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w0)) ->
  getr regs 11 = Z_to_bv 64 d11 ->
  getr regs 12 = Z_to_bv 64 d12 ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  tv_ok d11 ->
  (0 <= d12 <= 255)%Z ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f134) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f16c) m' rom)
    /\ mframe [((bytea (bufs2 + w0))%Z, 1%Z)] m m'
    /\ regs_agree (fun r => In r [11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m d11 d12 BT S0 H7 H10 H11 H12 H15 DC11 DC12.
  dl_facts.
  pose proof (tv_range _ DC11) as RG11.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; w0; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d11; d12] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; w0; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; 0%Z; d11; d12]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 0 19999; KRange (EVar 57) 0 255]) by (ex_know regs).
  dl_run 400%nat [127340%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1f048f : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 11) (Z_to_bv 64 255) = false ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w0))) 1 = true ->
  getr regs 7 = Z_to_bv 64 30 ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w0)) ->
  getr regs 12 = Z_to_bv 64 255 ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f14c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f16c) m' rom)
    /\ mframe [((bytea (bufs2 + w0))%Z, 1%Z)] m m'
    /\ getr regs' 11 = Z_to_bv 64 255
    /\ regs_agree (fun r => In r [11]%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H7 H10 H12 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; w0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; w0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 0 19999]) by (ex_know regs).
  dl_run 400%nat [127340%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma vt0_1f048t : forall (fx : FPState) regs m ,
  branch_taken BC_LT (getr regs 11) (Z_to_bv 64 255) = true ->
  store_ok SEGS m (Z_to_bv 64 (bytea (bufs2 + w0))) 1 = true ->
  getr regs 7 = Z_to_bv 64 30 ->
  getr regs 10 = Z_to_bv 64 (bytea (bufs2 + w0)) ->
  getr regs 12 = Z_to_bv 64 255 ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f14c) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f16c) m' rom)
    /\ mframe [((bytea (bufs2 + w0))%Z, 1%Z)] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT S0 H7 H10 H12 H15.
  dl_facts.
  ex_entry regs [lined; bufs1; bufs2; tabval; tab38; w0] HR.
  assert (HK : know_ok SEGS (ex_env regs [lined; bufs1; bufs2; tabval; tab38; w0]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 4; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 0 19999]) by (ex_know regs).
  dl_run 400%nat [127340%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Local Abbreviation vt0_1ef44_cells := (vt0_1ef44_cells_def lined bufs1 bufs2 tabval tab38 w0 wpl wpld).
Lemma vt0_1ef44_path : forall (fx : FPState) regs m,
  cells_ok SEGS m vt0_1ef44_cells ->
  tab_rd SEGS false (fun _ => True) vt0_1ef44_cells m tabval ->
  tab_rd SEGS true tv_ok vt0_1ef44_cells m tab38 ->
  getr regs 10 = Z_to_bv 64 lined ->
  getr regs 11 = Z_to_bv 64 w0 ->
  getr regs 12 = Z_to_bv 64 bufs1 ->
  getr regs 13 = Z_to_bv 64 bufs2 ->
  getr regs 14 = Z_to_bv 64 tabval ->
  getr regs 15 = Z_to_bv 64 tab38 ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1f048) m rom) (@mkst fx regs' (Z_to_bv 64 0x1f16c) m' rom)
    /\ mframe vt0_1ef44_cells m m'
    /\ getr regs' 7 = Z_to_bv 64 30
    /\ getr regs' 10 = Z_to_bv 64 (bytea (bufs2 + w0))
    /\ regs_agree (fun r => In r [5; 6; 7; 10; 11; 12; 13; 14; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m CK TR_tabval_false TR_tab38_true H10 H11 H12 H13 H14 H15.
  pose proof (mframe_refl vt0_1ef44_cells m) as FK0.
  destruct (cells_ok_read SEGS m m vt0_1ef44_cells (bytea (bufs1 + w0))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_0 Rd1_0].
  destruct (cells_ok_read SEGS m m vt0_1ef44_cells (lined + (4 * (w0 / 16)))%Z 4%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_1 Rd1_1].
  destruct (TR_tabval_false m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_2 & Rd1_2 & TV1_2).
  destruct (TR_tab38_true m (rdv false 1 bs1_0)%Z FK0 ltac:(dl_u8)) as (bs1_3 & Rd1_3 & TV1_3).
  destruct (cells_ok_read SEGS m m vt0_1ef44_cells (bytea (bufs2 + w0))%Z 1%Z wr_readable_img CK (proj1 FK0) ltac:(dl_in0)) as [bs1_4 Rd1_4].
  destruct (vt0_1ef44 fx regs m bs1_0 bs1_1 bs1_2 bs1_3 bs1_4 Rd1_0 Rd1_1 Rd1_2 Rd1_3 Rd1_4 TV1_3 (cells_ok_sok SEGS m m vt0_1ef44_cells (lined + (4 * (w0 / 16)))%Z 4%Z CK (proj1 FK0) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r1 & m1 & RUN1 & FR1 & E1_7 & E1_10 & E1_11 & E1_12 & AG1).
  assert (FK1 : mframe vt0_1ef44_cells m m1) by (apply (mframe_step _ _ _ _ _ FK0 FR1); unfold vt0_1ef44_cells_def; dl_incl).
  assert (DX : exists d, getr r1 11 = Z_to_bv 64 d /\ tv_ok d) by (eexists; split; [dl_get | dl_dclass]).
  destruct DX as (d2_11 & DE2_11 & DC2_11).
  assert (DX : exists d, getr r1 12 = Z_to_bv 64 d /\ (0 <= d <= 255)%Z) by (eexists; split; [dl_get | dl_dclass]).
  destruct DX as (d2_12 & DE2_12 & DC2_12).
  destruct (branch_taken BC_LT (Z_to_bv 64 d2_11) (Z_to_bv 64 0)) eqn:B1.
  - (* [comment removed for export] *)
    destruct (vt0_1f030t fx r1 m1 d2_11 d2_12 B1 (cells_ok_sok SEGS m m1 vt0_1ef44_cells (bytea (bufs2 + w0))%Z 1%Z CK (proj1 FK1) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) DC2_11 DC2_12) as (r2 & m2 & RUN2 & FR2 & AG2).
    assert (FK2 : mframe vt0_1ef44_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold vt0_1ef44_cells_def; dl_incl).
    exists r2, m2. split; [exact (msteps_trans _ _ _ _ RUN1 RUN2)|]. split; [exact FK2|].
    repeat split; [dl_get .. | ra_chain].
  - (* [comment removed for export] *)
    destruct (vt0_1f030f fx r1 m1 d2_11 d2_12 B1 ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) DC2_11 DC2_12) as (r2 & m2 & RUN2 & FR2 & E2_12 & AG2).
    assert (FK2 : mframe vt0_1ef44_cells m m2) by (apply (mframe_step _ _ _ _ _ FK1 FR2); unfold vt0_1ef44_cells_def; dl_incl).
    destruct (branch_taken BC_LT (getr r2 11) (Z_to_bv 64 255)) eqn:B2.
    + (* [comment removed for export] *)
      destruct (vt0_1f048t fx r2 m2  B2 (cells_ok_sok SEGS m m2 vt0_1ef44_cells (bytea (bufs2 + w0))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & AG3).
      assert (FK3 : mframe vt0_1ef44_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold vt0_1ef44_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
    + (* [comment removed for export] *)
      destruct (vt0_1f048f fx r2 m2  B2 (cells_ok_sok SEGS m m2 vt0_1ef44_cells (bytea (bufs2 + w0))%Z 1%Z CK (proj1 FK2) ltac:(dl_in0)) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get) ltac:(dl_get)) as (r3 & m3 & RUN3 & FR3 & E3_11 & AG3).
      assert (FK3 : mframe vt0_1ef44_cells m m3) by (apply (mframe_step _ _ _ _ _ FK2 FR3); unfold vt0_1ef44_cells_def; dl_incl).
      exists r3, m3. split; [exact (msteps_trans _ _ _ _ RUN1 (msteps_trans _ _ _ _ RUN2 RUN3))|]. split; [exact FK3|].
      repeat split; [dl_get .. | ra_chain].
Qed.

End VT0.
