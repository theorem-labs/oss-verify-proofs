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

(* [comment removed for export] *)
Definition ua_hyps (s datad datat bufs1 bufs2 w h wplt : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= datat <= 140737488355328)%Z /\ (datat mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wplt <= 5000)%Z.
Section UA.
Variable rom : word -> option byte.
Variables (s datad datat bufs1 bufs2 w h wplt : Z).
Hypothesis HYP : ua_hyps s datad datat bufs1 bufs2 w h wplt.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_datat & A_datat & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_w & R_h & R_wplt); idtac.
(* [comment removed for export] *)
Lemma ua_1cb90 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 176)) 8 = true ->
  rdn SEGS m (Z_to_bv 64 (s - 108)) 4 = Some (Z_to_le_bytes 4 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 112)) 4 = Some (Z_to_le_bytes 4 h) ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wplt) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 datat) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 25 = Z_to_bv 64 datad ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cc94) m rom) (@mkst fx regs' (Z_to_bv 64 0x326c4) m' rom)
    /\ mframe [((s - 176)%Z, 8%Z)] m m'
    /\ getr regs' 1 = Z_to_bv 64 117980
    /\ getr regs' 8 = Z_to_bv 64 h
    /\ getr regs' 10 = Z_to_bv 64 bufs2
    /\ getr regs' 11 = Z_to_bv 64 datat
    /\ getr regs' 12 = Z_to_bv 64 (wplt * 4)
    /\ getr regs' 26 = Z_to_bv 64 datat
    /\ getr regs' 27 = Z_to_bv 64 (wplt * 4)
    /\ rdn SEGS m' (Z_to_bv 64 (s - 176)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w))
    /\ regs_agree (fun r => In r [1; 8; 10; 11; 12; 26; 27]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 KC0 KC1 KC2 KC3 H2 H9 H18 H25.
  dl_facts.
  ex_entry regs [s; datad; datat; bufs1; bufs2; w; h; wplt] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; datat; bufs1; bufs2; w; h; wplt]) m [KWord (SA (EVar 32) (-108)) 4 (EVar 37); KWord (SA (EVar 32) (-112)) 4 (EVar 38); KWord (SA (EVar 32) (-152)) 8 (EVar 39); KWord (SA (EVar 32) (-160)) 8 (EVar 34); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 1 20000; KRange (EVar 38) 1 20000; KRange (EVar 39) 1 5000]) by (ex_know regs).
  dl_run 400%nat [206532%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 |  ex_agree HR HR'].
Qed.

End UA.

(* [comment removed for export] *)
Definition ub_hyps (s datad datat bufs1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= datat <= 140737488355328)%Z /\ (datat mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z.
Section UB.
Variable rom : word -> option byte.
Variables (s datad datat bufs1 : Z).
Hypothesis HYP : ub_hyps s datad datat bufs1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_datat & A_datat & R_bufs1 & A_bufs1); idtac.
(* [comment removed for export] *)
Lemma ub_1cbd8 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 192)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 200)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 1 ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 25 = Z_to_bv 64 datad ->
  getr regs 26 = Z_to_bv 64 datat ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ccdc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1cddc) m' rom)
    /\ mframe [((s - 192)%Z, 8%Z); ((s - 200)%Z, 8%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ rdn SEGS m' (Z_to_bv 64 (s - 192)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 200)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ regs_agree (fun r => In r [10; 11]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 H2 H8 H9 H25 H26.
  dl_facts.
  ex_entry regs [s; datad; datat; bufs1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; datat; bufs1]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4]) by (ex_know regs).
  dl_run 400%nat [118236%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End UB.

(* [comment removed for export] *)
Definition uc_hyps (s datad datat bufs1 h2 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= datat <= 140737488355328)%Z /\ (datat mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (2 <= h2 <= 20000)%Z.
Section UC.
Variable rom : word -> option byte.
Variables (s datad datat bufs1 h2 : Z).
Hypothesis HYP : uc_hyps s datad datat bufs1 h2.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_datat & A_datat & R_bufs1 & A_bufs1 & R_h2); idtac.
(* [comment removed for export] *)
Lemma uc_1cbd8 : forall (fx : FPState) regs m ,
  store_ok SEGS m (Z_to_bv 64 (s - 192)) 8 = true ->
  store_ok SEGS m (Z_to_bv 64 (s - 200)) 8 = true ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 h2 ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 25 = Z_to_bv 64 datad ->
  getr regs 26 = Z_to_bv 64 datat ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1ccdc) m rom) (@mkst fx regs' (Z_to_bv 64 0x1cd08) m' rom)
    /\ mframe [((s - 192)%Z, 8%Z); ((s - 200)%Z, 8%Z)] m m'
    /\ getr regs' 10 = Z_to_bv 64 0
    /\ getr regs' 11 = Z_to_bv 64 0
    /\ getr regs' 19 = Z_to_bv 64 1
    /\ getr regs' 23 = Z_to_bv 64 1
    /\ getr regs' 24 = Z_to_bv 64 1
    /\ rdn SEGS m' (Z_to_bv 64 (s - 192)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0))
    /\ rdn SEGS m' (Z_to_bv 64 (s - 200)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (h2 - 1)))
    /\ regs_agree (fun r => In r [10; 11; 19; 23; 24]%list) regs regs'.
Proof using All.
  intros fx regs m  S0 S1 H2 H8 H9 H25 H26.
  dl_facts.
  ex_entry regs [s; datad; datat; bufs1; h2] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; datat; bufs1; h2]) m [KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 2 20000]) by (ex_know regs).
  dl_run 400%nat [118024%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_saved0 | dl_saved0 |  ex_agree HR HR'].
Qed.

End UC.

(* [comment removed for export] *)
Definition ur_hyps (s datad datat bufs1 bufs2 tabval tab38 tab14 w h wplt wpld i1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= datat <= 140737488355328)%Z /\ (datat mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (4096 <= tab14 <= 140737488355328)%Z /\ (tab14 mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= h <= 20000)%Z /\ (1 <= wplt <= 5000)%Z /\ (1 <= wpld <= 1250)%Z /\ (1 <= i1 <= 19999)%Z /\ (1 <= i1 < h)%Z /\ (0 <= i1 * wplt < 2 ^ 24)%Z /\ (0 <= (i1 - 1) * wpld < 2 ^ 24)%Z.
Section UR.
Variable rom : word -> option byte.
Variables (s datad datat bufs1 bufs2 tabval tab38 tab14 w h wplt wpld i1 : Z).
Hypothesis HYP : ur_hyps s datad datat bufs1 bufs2 tabval tab38 tab14 w h wplt wpld i1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_datat & A_datat & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_tabval & A_tabval & R_tab38 & A_tab38 & R_tab14 & A_tab14 & R_w & R_h & R_wplt & R_wpld & R_i1 & Hi & Hps & Hpd); idtac.
(* [comment removed for export] *)
Lemma ur_1cc04 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wplt) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 h ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 1 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 23 = Z_to_bv 64 i1 ->
  getr regs 24 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 datad ->
  getr regs 26 = Z_to_bv 64 datat ->
  getr regs 27 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cd08) m rom) (@mkst fx regs' (Z_to_bv 64 0x326c4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 118040
    /\ getr regs' 10 = Z_to_bv 64 bufs1
    /\ getr regs' 11 = Z_to_bv 64 bufs2
    /\ getr regs' 12 = Z_to_bv 64 (wplt * 4)
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1]) m [KWord (SA (EVar 32) (-152)) 8 (EVar 42); KWord (SA (EVar 32) (-160)) 8 (EVar 34); KWord (SA (EVar 32) (-168)) 8 (EVar 43); KWord (SA (EVar 32) (-176)) 8 (EVar 40); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 1 20000; KRange (EVar 41) 1 20000; KRange (EVar 42) 1 5000; KRange (EVar 43) 1 1250; KRange (EVar 44) 1 19999]) by (ex_know regs).
  dl_run 400%nat [118024%Z; 118236%Z; 125956%Z; 206532%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ur_1cc14 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wplt) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 h ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 1 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 23 = Z_to_bv 64 i1 ->
  getr regs 24 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 datad ->
  getr regs 26 = Z_to_bv 64 datat ->
  getr regs 27 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cd18) m rom) (@mkst fx regs' (Z_to_bv 64 0x326c4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 118128
    /\ getr regs' 9 = Z_to_bv 64 (i1 - 1)
    /\ getr regs' 10 = Z_to_bv 64 bufs2
    /\ getr regs' 11 = Z_to_bv 64 (datat + (4 * (i1 * wplt)))
    /\ getr regs' 12 = Z_to_bv 64 (wplt * 4)
    /\ getr regs' 25 = Z_to_bv 64 bufs1
    /\ getr regs' 26 = Z_to_bv 64 datad
    /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 25; 26]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1]) m [KWord (SA (EVar 32) (-152)) 8 (EVar 42); KWord (SA (EVar 32) (-160)) 8 (EVar 34); KWord (SA (EVar 32) (-168)) 8 (EVar 43); KWord (SA (EVar 32) (-176)) 8 (EVar 40); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 1 20000; KRange (EVar 41) 1 20000; KRange (EVar 42) 1 5000; KRange (EVar 43) 1 1250; KRange (EVar 44) 1 19999]) by (ex_know regs).
  dl_run 400%nat [118024%Z; 118236%Z; 125956%Z; 206532%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ur_1cc6c : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wplt) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 h ->
  getr regs 9 = Z_to_bv 64 (i1 - 1) ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 1 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 23 = Z_to_bv 64 i1 ->
  getr regs 24 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 bufs1 ->
  getr regs 26 = Z_to_bv 64 datad ->
  getr regs 27 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cd70) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ec04) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 118228
    /\ getr regs' 9 = Z_to_bv 64 bufs1
    /\ getr regs' 10 = Z_to_bv 64 (datad + (4 * ((i1 - 1) * wpld)))
    /\ getr regs' 11 = Z_to_bv 64 w
    /\ getr regs' 12 = Z_to_bv 64 bufs1
    /\ getr regs' 13 = Z_to_bv 64 bufs2
    /\ getr regs' 14 = Z_to_bv 64 tabval
    /\ getr regs' 15 = Z_to_bv 64 tab38
    /\ getr regs' 16 = Z_to_bv 64 tab14
    /\ getr regs' 17 = Z_to_bv 64 0
    /\ getr regs' 25 = Z_to_bv 64 datad
    /\ getr regs' 26 = Z_to_bv 64 datat
    /\ regs_agree (fun r => In r [1; 9; 10; 11; 12; 13; 14; 15; 16; 17; 25; 26]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1]) m [KWord (SA (EVar 32) (-152)) 8 (EVar 42); KWord (SA (EVar 32) (-160)) 8 (EVar 34); KWord (SA (EVar 32) (-168)) 8 (EVar 43); KWord (SA (EVar 32) (-176)) 8 (EVar 40); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 1 20000; KRange (EVar 41) 1 20000; KRange (EVar 42) 1 5000; KRange (EVar 43) 1 1250; KRange (EVar 44) 1 19999]) by (ex_know regs).
  dl_run 400%nat [118024%Z; 118236%Z; 125956%Z; 206532%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ur_1ccd0 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wplt) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 h ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 1 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 23 = Z_to_bv 64 i1 ->
  getr regs 24 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 datad ->
  getr regs 26 = Z_to_bv 64 datat ->
  getr regs 27 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cdd4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1cdd8) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 23 = Z_to_bv 64 (i1 + 1)
    /\ regs_agree (fun r => In r [23]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1]) m [KWord (SA (EVar 32) (-152)) 8 (EVar 42); KWord (SA (EVar 32) (-160)) 8 (EVar 34); KWord (SA (EVar 32) (-168)) 8 (EVar 43); KWord (SA (EVar 32) (-176)) 8 (EVar 40); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 1 20000; KRange (EVar 41) 1 20000; KRange (EVar 42) 1 5000; KRange (EVar 43) 1 1250; KRange (EVar 44) 1 19999]) by (ex_know regs).
  dl_run 400%nat [118024%Z; 118236%Z; 125956%Z; 206532%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ur_1ccd4f : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 h) (Z_to_bv 64 (i1 + 1)) = false ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wplt) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 h ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 1 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 23 = Z_to_bv 64 (i1 + 1) ->
  getr regs 24 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 datad ->
  getr regs 26 = Z_to_bv 64 datat ->
  getr regs 27 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cdd8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1cddc) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1]) m [KWord (SA (EVar 32) (-152)) 8 (EVar 42); KWord (SA (EVar 32) (-160)) 8 (EVar 34); KWord (SA (EVar 32) (-168)) 8 (EVar 43); KWord (SA (EVar 32) (-176)) 8 (EVar 40); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 1 20000; KRange (EVar 41) 1 20000; KRange (EVar 42) 1 5000; KRange (EVar 43) 1 1250; KRange (EVar 44) 1 19999]) by (ex_know regs).
  dl_run 400%nat [118024%Z; 118236%Z; 125956%Z; 206532%Z] (SCR [false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ur_1ccd4t : forall (fx : FPState) regs m ,
  branch_taken BC_NE (Z_to_bv 64 h) (Z_to_bv 64 (i1 + 1)) = true ->
  rdn SEGS m (Z_to_bv 64 (s - 152)) 8 = Some (Z_to_le_bytes 8 wplt) ->
  rdn SEGS m (Z_to_bv 64 (s - 160)) 8 = Some (Z_to_le_bytes 8 datat) ->
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 8 = Z_to_bv 64 h ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 19 = Z_to_bv 64 1 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 23 = Z_to_bv 64 (i1 + 1) ->
  getr regs 24 = Z_to_bv 64 1 ->
  getr regs 25 = Z_to_bv 64 datad ->
  getr regs 26 = Z_to_bv 64 datat ->
  getr regs 27 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cdd8) m rom) (@mkst fx regs' (Z_to_bv 64 0x1cd08) m' rom)
    /\ mframe [] m m'
    /\ regs_agree (fun r => In r []%list) regs regs'.
Proof using All.
  intros fx regs m  BT KC0 KC1 KC2 KC3 H2 H8 H9 H18 H19 H20 H21 H22 H23 H24 H25 H26 H27.
  dl_facts.
  ex_entry regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; datat; bufs1; bufs2; tabval; tab38; tab14; w; h; wplt; wpld; i1]) m [KWord (SA (EVar 32) (-152)) 8 (EVar 42); KWord (SA (EVar 32) (-160)) 8 (EVar 34); KWord (SA (EVar 32) (-168)) 8 (EVar 43); KWord (SA (EVar 32) (-176)) 8 (EVar 40); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 4096 140737488355328; KAlign (EVar 39) 4; KRange (EVar 40) 1 20000; KRange (EVar 41) 1 20000; KRange (EVar 42) 1 5000; KRange (EVar 43) 1 1250; KRange (EVar 44) 1 19999]) by (ex_know regs).
  dl_run 400%nat [118024%Z; 118236%Z; 125956%Z; 206532%Z] (SCR [true] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [ ex_agree HR HR'].
Qed.

End UR.

(* [comment removed for export] *)
Definition ux_hyps (s datad bufs1 bufs2 tabval tab38 tab14 w wplt wpld h1 : Z) : Prop :=
  (4096 <= s <= 140737488355328)%Z /\ (s mod 16 = 0)%Z /\ (4096 <= datad <= 140737488355328)%Z /\ (datad mod 4 = 0)%Z /\ (4096 <= bufs1 <= 140737488355328)%Z /\ (bufs1 mod 4 = 0)%Z /\ (4096 <= bufs2 <= 140737488355328)%Z /\ (bufs2 mod 4 = 0)%Z /\ (4096 <= tabval <= 140737488355328)%Z /\ (tabval mod 4 = 0)%Z /\ (4096 <= tab38 <= 140737488355328)%Z /\ (tab38 mod 4 = 0)%Z /\ (4096 <= tab14 <= 140737488355328)%Z /\ (tab14 mod 4 = 0)%Z /\ (1 <= w <= 20000)%Z /\ (1 <= wplt <= 5000)%Z /\ (1 <= wpld <= 1250)%Z /\ (0 <= h1 <= 19999)%Z /\ (0 <= h1 * wpld < 2 ^ 24)%Z.
Section UX.
Variable rom : word -> option byte.
Variables (s datad bufs1 bufs2 tabval tab38 tab14 w wplt wpld h1 : Z).
Hypothesis HYP : ux_hyps s datad bufs1 bufs2 tabval tab38 tab14 w wplt wpld h1.
Ltac dl_facts := pose proof HYP as (R_s & A_s & R_datad & A_datad & R_bufs1 & A_bufs1 & R_bufs2 & A_bufs2 & R_tabval & A_tabval & R_tab38 & A_tab38 & R_tab14 & A_tab14 & R_w & R_wplt & R_wpld & R_h1 & Hpd); idtac.
(* [comment removed for export] *)
Lemma ux_1ccd8 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 25 = Z_to_bv 64 datad ->
  getr regs 27 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cddc) m rom) (@mkst fx regs' (Z_to_bv 64 0x326c4) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 118260
    /\ getr regs' 10 = Z_to_bv 64 bufs1
    /\ getr regs' 11 = Z_to_bv 64 bufs2
    /\ getr regs' 12 = Z_to_bv 64 (wplt * 4)
    /\ regs_agree (fun r => In r [1; 10; 11; 12]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H9 H18 H20 H21 H22 H25 H27.
  dl_facts.
  ex_entry regs [s; datad; bufs1; bufs2; tabval; tab38; tab14; w; wplt; wpld; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; bufs1; bufs2; tabval; tab38; tab14; w; wplt; wpld; h1]) m [KWord (SA (EVar 32) (-168)) 8 (EVar 41); KWord (SA (EVar 32) (-176)) 8 (EVar 39); KWord (SA (EVar 32) (-192)) 8 (ELit 0); KWord (SA (EVar 32) (-200)) 8 (EVar 42); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 1 20000; KRange (EVar 40) 1 5000; KRange (EVar 41) 1 1250; KRange (EVar 42) 0 19999]) by (ex_know regs).
  dl_run 400%nat [125956%Z; 206532%Z] (SCR [] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

(* [comment removed for export] *)
Lemma ux_1ccf0 : forall (fx : FPState) regs m ,
  rdn SEGS m (Z_to_bv 64 (s - 168)) 8 = Some (Z_to_le_bytes 8 wpld) ->
  rdn SEGS m (Z_to_bv 64 (s - 176)) 8 = Some (Z_to_le_bytes 8 w) ->
  rdn SEGS m (Z_to_bv 64 (s - 192)) 8 = Some (Z_to_le_bytes 8 0) ->
  rdn SEGS m (Z_to_bv 64 (s - 200)) 8 = Some (Z_to_le_bytes 8 h1) ->
  getr regs 2 = Z_to_bv 64 (s - 208) ->
  getr regs 9 = Z_to_bv 64 bufs1 ->
  getr regs 18 = Z_to_bv 64 bufs2 ->
  getr regs 20 = Z_to_bv 64 tabval ->
  getr regs 21 = Z_to_bv 64 tab38 ->
  getr regs 22 = Z_to_bv 64 tab14 ->
  getr regs 25 = Z_to_bv 64 datad ->
  getr regs 27 = Z_to_bv 64 (wplt * 4) ->
  exists regs' m', msteps SEGS (@mkst fx regs (Z_to_bv 64 0x1cdf4) m rom) (@mkst fx regs' (Z_to_bv 64 0x1ec04) m' rom)
    /\ mframe [] m m'
    /\ getr regs' 1 = Z_to_bv 64 118356
    /\ getr regs' 10 = Z_to_bv 64 (datad + (4 * (h1 * wpld)))
    /\ getr regs' 11 = Z_to_bv 64 w
    /\ getr regs' 12 = Z_to_bv 64 bufs1
    /\ getr regs' 13 = Z_to_bv 64 bufs2
    /\ getr regs' 14 = Z_to_bv 64 tabval
    /\ getr regs' 15 = Z_to_bv 64 tab38
    /\ getr regs' 16 = Z_to_bv 64 tab14
    /\ getr regs' 17 = Z_to_bv 64 1
    /\ regs_agree (fun r => In r [1; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs regs'.
Proof using All.
  intros fx regs m  KC0 KC1 KC2 KC3 H2 H9 H18 H20 H21 H22 H25 H27.
  dl_facts.
  ex_entry regs [s; datad; bufs1; bufs2; tabval; tab38; tab14; w; wplt; wpld; h1] HR.
  assert (HK : know_ok SEGS (ex_env regs [s; datad; bufs1; bufs2; tabval; tab38; tab14; w; wplt; wpld; h1]) m [KWord (SA (EVar 32) (-168)) 8 (EVar 41); KWord (SA (EVar 32) (-176)) 8 (EVar 39); KWord (SA (EVar 32) (-192)) 8 (ELit 0); KWord (SA (EVar 32) (-200)) 8 (EVar 42); KRange (EVar 32) 4096 140737488355328; KAlign (EVar 32) 16; KRange (EVar 33) 4096 140737488355328; KAlign (EVar 33) 4; KRange (EVar 34) 4096 140737488355328; KAlign (EVar 34) 4; KRange (EVar 35) 4096 140737488355328; KAlign (EVar 35) 4; KRange (EVar 36) 4096 140737488355328; KAlign (EVar 36) 4; KRange (EVar 37) 4096 140737488355328; KAlign (EVar 37) 4; KRange (EVar 38) 4096 140737488355328; KAlign (EVar 38) 4; KRange (EVar 39) 1 20000; KRange (EVar 40) 1 5000; KRange (EVar 41) 1 1250; KRange (EVar 42) 0 19999]) by (ex_know regs).
  dl_run 400%nat [125956%Z; 206532%Z] (SCR [false; false] [] []) HR HK R' HR' Hms.
  exists R'. eexists. split; [exact Hms|]. dl_mem_norm regs. split; [dl_frame0|].
  repeat split; [dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' | dl_reg regs HR' |  ex_agree HR HR'].
Qed.

End UX.
