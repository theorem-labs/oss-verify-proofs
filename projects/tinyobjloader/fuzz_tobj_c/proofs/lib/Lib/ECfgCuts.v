(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "lnode"; "lmeas"; "ln_rank"; "ln_state"; "LMAX"; "SPfamE"; "edge"; "enode"; "ln_vars"; "to_enodeL"; "vdir"; "echeck2"; "leaves_edges"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "agree_below"; "sstate"; "sv"; "ss_lenient"; "ss_next"; "@Corelib.Init.Datatypes"; "list"; "option"; "bool"; "andb"; "false"; "length"; "prod"; "true"; "Some"; "app"; "nat"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "@Stdlib.ZArith.BinInt.Z"; "le"; "add"; "lt"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "LQ"; "@Stdlib.Lists.List"; "In"; "forallb"; "nth_error"; "@Corelib.Lists.ListDef"; "map"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "leaf"; "RsSymJump"; "mkLeaf"; "sym_run"; "@Corelib.Init.Logic"; "eq"; "or"; "and"; "@Corelib.Init.Peano"; "le"; "@Corelib.Numbers.BinNums"; "positive"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ECfgCuts.S"; "elcut"; "@Stdlib.PArith.BinPos.Pos"; "leb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import TobjJVx.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section S.
Variable segs : list Segment.
Variables (fuel : nat) (cutpcs : list Z) (g : positive).

Definition elcut (nodes : list lnode) (i : nat) (n : lnode) : bool := ltac2:(tb__ "0|3|
S16S1eS11S3Vn;A1M0A1A1S16S36Vg;S12G0A1A2S14S13S2cA1M1A1S15Lx;S2fVsegs;Vfuel;Vcutpcs;G0S1aA5G1S14S13S6A1M2A1S15Lx;ScVg;Vi;R1S29S0SfS3Vnodes;A4A4G2S27S6SbVg;Vnodes;A2R1A3Les;S17X14x2Lleaves;S17X14x2A2A2").

Theorem cfg_complete_auto2_cuts : ltac2:(tb__ "0|2|
S13S0A1M0G0SdOF_;S13S2bA1S2aOF_;F_;S1fOF_;SdSdR5R2A1SeVg;R3R2A3R7R3A1F_;F_;Fr2;Fr1;S1dS0S30S14S0A1S28S0R8R2A3S1bS0R1A2A3S30S15S35S1cS0R9R8A3R3R2A3S1aA3F_;Fn;Fi;S0SdS26S0R2R8A3R8R2A1S20Vsegs;S24Vsegs;R8S3R4A1M1R3A4S1fS31S5Vsegs;R9S29S0S7S9RaA1RcA4S1R5R4A2R1A5R8R1A1A2Lw;A3F_;F_;Frho;FE;S0SdS26S0R2RaA3R9R2A1S20Vsegs;S24Vsegs;R9G1R3A4R8A3F_;F_;Frho;Fn;F_;F_;F_;FQ;FK;FG;Fexits;Fcuts;").
Proof using .
  intros cuts exits G K Q HG Hc Hexits n rho Hin Hg.
  destruct (cuts_edges_ok segs fuel cutpcs g (echeck2 g (cuts ++ exits)) (map ln_state cuts ++ map ln_state exits)
              (map ln_state cuts) 0) as (es & Hce & Hes).
  { intros k T Hn. rewrite nth_error_map in Hn. destruct (nth_error cuts k) as [nd|] eqn:En; [|discriminate].
    cbn in Hn. injection Hn as <-.
    pose proof (Hc k nd En) as H. unfold elcut in H. apply andb_prop in H as [_ H]. apply andb_prop in H as [Hg' H].
    split; [exact Hg'|].
    destruct (sym_run segs fuel cutpcs (ln_state nd) true) as [leaves|]; [|discriminate].
    cbn [Nat.add].
    destruct (leaves_edges g k leaves (map ln_state (cuts ++ exits))) as [es|] eqn:Hle; [|discriminate].
    exists leaves, es. rewrite map_app in Hle. auto. }
  change (ln_state n) with (en_state (to_enodeL G n)).
  apply (cfg_complete_gen segs fuel cutpcs g (map (to_enodeL G) cuts) (map (to_enodeL G) exits) es K Q).
  - apply forallb_forall. intros x Hx. apply in_map_iff in Hx as (n' & <- & Hn'). apply In_nth_error in Hn' as [i Hi].
    pose proof (Hc i n' Hi) as H. unfold elcut in H. apply andb_prop in H as [H _]. exact H.
  - unfold cfg_edges. rewrite !map_map. cbn [to_enodeL en_state fst snd].
    change (fun x : lnode => ln_state x) with ln_state. exact Hce.
  - rewrite <- map_app. apply Forall_forall. intros e He. apply (echeck2_sound g G _ e HG).
    exact (proj1 (forallb_forall _ _) Hes e He).
  - intros E rho' HinE HgE. apply in_map_iff in HinE as (n' & <- & Hn'). exact (Hexits n' rho' Hn' HgE).
  - apply in_map. exact Hin.
  - exact Hg.
Qed.

Lemma eexit_post_L : ltac2:(tb__ "0|0|
S13S2bA1S2aOF_;F_;S34SdS1fOF_;S13S2cA1SfS26S2cS2eR1S2dA2R2A3SdSeR7R6R1A3S20Vsegs;S24Vsegs;R9R4R2A4S1fS31R7R1A1S25Vsegs;RaR9R8R6R1A6A2Lw;A3F_;Frho;F_;FP;Fposts;FX;Frho0;Fn;FK;").
Proof using .
  intros K n rho0 X posts P Hin rho Hag w [Hsm Hk]. exists w. split; [apply wsteps_refl|].
  right. exists (mkLeaf P RsSymJump), rho. auto.
Qed.

Lemma lmeas_rank_lt : ltac2:(tb__ "0|3|
S0S0SdSdS21Z0M0S2R4A1M1A2S21S22S2R5A1Z1A2G1A2S33S18S19SaS10A2S8R6A1A2S4A2S32S21G0S1R7R5A2M2A2S23G2S1R6R4A2A2A2F_;F_;F_;Fr2;Fr1;FE;FC;").
Proof using .
  intros C E r1 r2 H0 Hlt Hlen. split; [apply lmeas_nonneg; exact H0|].
  unfold lmeas. pose proof (lex_part_bound r1 (ln_vars C) Hlen) as B1.
  pose proof (lex_val_range r2 (ln_vars E)) as B2. pose proof (B64_pos (LMAX - length (ln_vars E))) as P2.
  pose proof (B64_pos LMAX) as P. nia.
Qed.

Lemma reenter_L : ltac2:(tb__ "0|1|
S13S2bA1S2aOF_;F_;SdOF_;S13S0A1S0S0SdSdS1fS26S0R5R6A3R8R4A1S24Vsegs;RaS3R7A1R5R3A5S21Z0S2R8A1M0A2S21S22S2R9A1Z1A2G0A2S33S18S19SaS10A2S8RaA1A2S4A2S5Vsegs;ReS29S0S7S9RdA1RcA4S1RaR8A2R7A5F_;F_;F_;F_;F_;F_;Fw;FrhoE;FrhoC;FE;FC;Fcuts;FG;FK;").
Proof using .
  intros K G cuts C E rhoC rhoE w Hin Hg Hsp H0 Hlt Hlen.
  exists (to_enodeL G C), rhoC. split; [apply in_map; exact Hin|].
  cbn [to_enodeL en_state en_ghost en_meas fst snd]. split; [exact Hg|]. split; [exact Hsp|].
  apply lmeas_rank_lt; assumption.
Qed.
End S.
