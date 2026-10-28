(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1cd X1bu X1cf X1cc X1bs X1c2 X1bn X1bj X1bk X1bq X1br X1c0.
From OssFuzzTheorems.speex.speex_decode_fuzzer_float.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Agent Require Import X0px X0qn X0qc X0qp X0qb X0pt.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1m2 X1m3 X1m5 X1fl X1ea X1fr X1h7 X1kd X1k9.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1nj. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1ik X1ij X1ii X1il.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1go X1hk. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Ref Require Import X1hl. From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.U Require Import X1gy.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1ra X1qu X1qx X1ri X1r3 X1r4 X1r6 X1qz X1r0 X1r1 X1nt X1rg X1rh X1re X1od.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bl.
From OssFuzzTheorems.Proofs.speex.speex_decode_fuzzer_float.lib.Lib Require Import X1bv.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma rauxv_ok_agree {RCEIL : RunCeiling} : forall (P : Z -> Prop) m m' B,
agree_on rsegs P m m' -> rauxv_ok m B ->
(forall a, RAUXV_CELL <= a < RAUXV_CELL + 8 -> P a) -> (forall a, B <= a -> P a) -> rauxv_ok m' B.
Proof.
intros P m m' B AG sfH_; first [ sf_destruct 14%nat sfH_ as av x3 x4 x5 x16 x6 x11 x12 x23 rnd C A1 A2 H | sf_fb; destruct sfH_ as (av & x3 & x4 & x5 & x16 & x6 & x11 & x12 & x23 & rnd & C & A1 & A2 & H) ]; intros HC HB.
first [ unshelve sf_eexists 10%nat; [ exact (av) | exact (x3) | exact (x4) | exact (x5) | exact (x16) | exact (x6) | exact (x11) | exact (x12) | exact (x23) | exact (rnd) | ] | sf_fb; exists av, x3, x4, x5, x16, x6, x11, x12, x23, rnd ].
split; [eapply rw_cells_agree; [exact AG| exact C| intros a Ha; apply HC; cbn in Ha; lia]|].
split; [eapply bytes_at_agree; [exact AG| exact A1| intros a Ha; apply HB; lia]|].
split; [eapply bytes_at_agree; [exact AG| exact A2| intros a Ha; apply HB; lia]|].
exact H.
Qed.

Definition hcaller_addr (c : hcx) (a : Z) : Prop :=
usp c <= a \/ (0x3b000 <= a < 0x6e000 /\ ~ (RSTDERR <= a < RSTDERR + 232)) \/ in_block (x_LB0 c) a.

Lemma hglob_agree {RCEIL : RunCeiling} : rheap_block_range_stmt -> forall (c : hcx) x h st m m' (P : Z -> Prop),
hcx_ok c -> hglob c x h st m -> agree_on rsegs P m m' ->
RHEAP st (a_LB x) m' -> mem_inv rsegs m' -> stk rsegs m' (x_lo c) (hsp c) -> stderr_wfile m' ->
(forall a, hcaller_addr c a -> P a) ->
hglob c x h st m'.
Proof.
intros RBR c x h st m m' P CX HG AG HP1 MI1 ST1 SEW1 PC.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
split; [exact HP1|]. split; [exact PERM|].
split. { eapply (pay_keep c _ _ _ CX AG PAY). intros NE IN a Ha. apply PC. right; right. exists (x_pb c, x_P c, zlength (x_payload c)). split; [exact IN| cbn; lia]. }
split. { eapply rtables_pristine_agree; [exact AG| | exact TP]. intros a Ha. apply PC. right; left. unfold RTABLES_LO, RTABLES_HI in *. lia. }
split; [exact SEW1|].
split. { exists errv. eapply rw_cells_agree; [exact AG| exact ERR|]. intros a Ha. apply PC. right; left. unfold RERRNO in *. cbn in Ha. lia. }
split. { eapply rauxv_ok_agree; [exact AG| exact AUX| |]; intros a Ha; apply PC; [right; left; unfold RAUXV_CELL in *; lia| left; lia]. }
split; [exact MI1|]. split; [exact ST1|].
split. { eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. apply PC. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]].
- left. exact Hc.
- right; left. split; [lia|]. intros Hs. apply Hx. cbn. left. cbn. exact Hs.
- right; right. exists bb. split; [exact Hbb| exact Rbb]. }
exact SO.
Qed.

Definition hfoot_ok (c : hcx) (x : hax) (h : hstate bptr) (iv : Z * Z) : Prop :=
(x_lo c <= fst iv /\ snd iv <= usp c)
\/ iv = (RSTDERR, RSTDERR + 232)
\/ (exists b, In b (owned x h) /\ blk_addr b <= fst iv /\ snd iv <= blk_addr b + blk_size b).

Lemma outside_of_foot {RCEIL : RunCeiling} : forall (c : hcx) x h W a,
Forall (hfoot_ok c x h) W ->
(forall b bb, In b (owned x h) -> In bb (x_LB0 c) ->
blk_addr b + blk_size b <= blk_addr bb \/ blk_addr bb + blk_size bb <= blk_addr b) ->
(forall b, In b (owned x h) -> rblock_range (blk_addr b) (blk_size b)) ->
(forall b, In b (x_LB0 c) -> rblock_range (blk_addr b) (blk_size b)) ->
alloc_ceiling <= x_lo c <= usp c ->
hcaller_addr c a -> outside W a.
Proof.
intros c x h W a FW DJ RO R0 XLO Ha. unfold alloc_ceiling in XLO.
induction W as [|[lo hi] W IH]; [exact I|].
inversion FW as [|iv W' F1 F2]; subst. split; [| apply IH; exact F2].
unfold hfoot_ok in F1. cbn [fst snd] in F1. unfold rblock_range, alloc_ceiling in RO, R0.
destruct F1 as [K|[K|(b & Hb & K1 & K2)]].
- destruct Ha as [Ha|[[Ha Hs]|(bb & Hbb & Rbb)]]; [ | lia |].
+   lia.
+ pose proof (R0 bb Hbb). lia.
- inversion K; subst.
destruct Ha as [Ha|[[Ha Hs]|(bb & Hbb & Rbb)]]; [ | lia |].
+ lia.
+ pose proof (R0 bb Hbb). lia.
- destruct Ha as [Ha|[[Ha Hs]|(bb & Hbb & Rbb)]].
+ pose proof (RO b Hb). lia.
+ pose proof (RO b Hb). lia.
+ pose proof (DJ b bb Hb Hbb). lia.
Qed.

Lemma hglob_munch {RCEIL : RunCeiling} : rheap_frame_stmt -> rheap_block_range_stmt -> rheap_blocks_nodup_stmt -> rheap_blocks_disjoint_stmt ->
forall (c : hcx) x h st m m' W,
hcx_ok c -> hglob c x h st m -> munch W m m' -> wmono rsegs m m' ->
mem_inv rsegs m' -> stk rsegs m' (x_lo c) (hsp c) -> stderr_wfile m' ->
Forall (hfoot_ok c x h) W ->
hglob c x h st m' /\ agree_on rsegs (fun a => outside W a) m m'.
Proof.
intros RHF RBR RND RBD c x h st m m' W CX HG MU WM MI1 ST1 SEW1 FW.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ]. unfold RFUZZ_STACK in LO.
pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof (agree_on_of_munch _ _ _ MU WM) as AG.
assert (HLo : forall b, In b (owned x h) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. exact Hb. }
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
pose proof (RND _ _ _ HP) as ND. pose proof (nodup_ids_perm _ _ PERM ND) as NDO.
assert (HP1 : RHEAP st (a_LB x) m').
{ eapply RHF; [exact HP| exact MU| exact WM|]. eapply Forall_impl; [| exact FW].
intros [lo hi] [K|[K|(b & Hb & K1 & K2)]]; cbn [fst snd] in *.
- left. cbn. lia.
- inversion K; subst. right; left. unfold RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RREPLACED. cbn. lia.
- right; right. exists b. split; [apply HLo; exact Hb| cbn; lia]. }
split; [| exact AG].
eapply (hglob_agree RBR c x h st m m' _ CX HG AG HP1 MI1 ST1 SEW1).
intros a Ha. apply (outside_of_foot c x h W a FW).
- intros b bb Hb Hbb. eapply (RBD _ _ _ _ _ HP); [apply HLo; exact Hb| apply HL0; exact Hbb|].
rewrite map_app in NDO. intros E. eapply (nodup_app_disj _ _ (blk_id b) NDO); [apply in_map; exact Hb| rewrite E; apply in_map; exact Hbb].
- intros b Hb. apply (RBR _ _ _ _ HP). apply HLo. exact Hb.
- intros b Hb. apply (RBR _ _ _ _ HP). apply HL0. exact Hb.
- lia.
- exact Ha.
Qed.

Lemma outside_blocks : forall (L : list block) a,
(forall b, In b L -> ~ (blk_addr b <= a < blk_addr b + blk_size b)) ->
outside (map (fun b => (blk_addr b, blk_addr b + blk_size b)) L) a.
Proof.
induction L as [|b L IH]; intros a H; [exact I|]. cbn [map outside]. split.
- apply H. left. reflexivity.
- apply IH. intros b' Hb'. apply H. right. exact Hb'.
Qed.

Lemma owned_apart {RCEIL : RunCeiling} : rheap_blocks_disjoint_stmt -> forall st m x (l1 l2 LB0 : list block) b1 b2,
RHEAP st (a_LB x) m -> List.NoDup (map blk_id (a_LB x)) -> Permutation (a_LB x) ((l1 ++ l2) ++ LB0) ->
In b1 l1 -> In b2 l2 -> blk_addr b1 + blk_size b1 <= blk_addr b2 \/ blk_addr b2 + blk_size b2 <= blk_addr b1.
Proof.
intros RBD st m x l1 l2 LB0 b1 b2 HP ND PERM H1 H2.
pose proof (nodup_ids_perm _ _ PERM ND) as ND'. rewrite <- app_assoc, map_app in ND'.
eapply (RBD _ _ _ _ _ HP).
- eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. apply in_app_iff. left. exact H1.
- eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. apply in_app_iff. right. exact H2.
- intros E. eapply (nodup_app_disj _ _ (blk_id b1) ND'); [apply in_map; exact H1|]. rewrite E, map_app. apply in_app_iff. left. apply in_map. exact H2.
Qed.

Lemma hrep_after_stackcall {RCEIL : RunCeiling} : forall dec_rep, dec_rep_frame_stmt dec_rep ->
rheap_frame_stmt -> rheap_block_range_stmt -> rheap_blocks_nodup_stmt -> rheap_blocks_disjoint_stmt ->
forall (c : hcx) x g st m m' cn cb (outb' stb' : list byte),
hcx_ok c -> hrep dec_rep c x g st m cn cb ->
munch [(x_lo c, aLOW c); (aOUT c, aOUT c + HOUT_BYTES); (aSTEREO c, aSTEREO c + 24)] m m' -> wmono rsegs m m' ->
mem_inv rsegs m' -> stk rsegs m' (x_lo c) (hsp c) ->
u8arr rsegs m' (aOUT c) outb' -> Z.of_nat (length outb') = 8000 -> rw_cells rsegs m' (aSTEREO c) [CB 24 stb'] ->
hrep dec_rep c x g st m' cn cb.
Proof.
intros dec_rep DRF RHF RBR RND RBD c x g st m m' cn cb outb' stb' CX HR MU WM MI' ST' OUT' LOUT' STB'.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
unfold RFUZZ_STACK in LO. pose proof CEIL as CEIL'. unfold alloc_ceiling in CEIL'.
pose proof HR as sfP_; first [ sf_destruct 16%nat sfP_ as (j16 & jsk & lk & LOW & LKOK) C1 C2 (stb & STB) OSP (opj & OP) (ogj & OG) SY BI (pad & FSZ) (outb & OUT & LOUT) (hij & HI) SAV DEC HG PURE | sf_fb; destruct sfP_ as ((j16 & jsk & lk & LOW & LKOK) & C1 & C2 & (stb & STB) & OSP & (opj & OP) & (ogj & OG) & SY & BI & (pad & FSZ) & (outb & OUT & LOUT) & (hij & HI) & SAV & DEC & HG & PURE) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
pose proof PURE as sfP_; first [ sf_destruct 8%nat sfP_ as SYOK BOK OWN SYBLK SYLEN BBR BSZ _ | sf_fb; destruct sfP_ as (SYOK & BOK & OWN & SYBLK & SYLEN & BBR & BSZ & _) ].
pose proof (agree_on_of_munch _ _ _ MU WM) as AG. unfold HOUT_BYTES in AG.
pose proof (rw_cells_bound _ _ _ _ LOW) as LB. unfold low_cells in LB. cbn [cells_size csize length Nat.add] in LB.
assert (OWF : forall a, (aLOW c <= a < aSTEREO c \/ aSTEREO c + 24 <= a < aOUT c \/ aOUT c + 8000 <= a) ->
outside [(x_lo c, aLOW c); (aOUT c, aOUT c + 8000); (aSTEREO c, aSTEREO c + 24)] a).
{ intros a Ha. cbn. repeat split; lia. }
assert (OWB : forall a, a < alloc_ceiling -> outside [(x_lo c, aLOW c); (aOUT c, aOUT c + 8000); (aSTEREO c, aSTEREO c + 24)] a).
{ intros a Ha. unfold alloc_ceiling in Ha. cbn. repeat split; lia. }
assert (HBLK : forall b a, In b (owned x g) -> blk_addr b <= a < blk_addr b + blk_size b -> a < alloc_ceiling).
{ intros b a Hb Ha. assert (Hb' : In b (a_LB x)). { eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. left. exact Hb. }
pose proof (RBR _ _ _ _ HP Hb') as sfP_; first [ sf_destruct 5%nat sfP_ as _ _ _ B4 _ | sf_fb; destruct sfP_ as (_ & _ & _ & B4 & _) ]. lia. }
assert (SEW' : stderr_wfile m').
{ eapply stderr_wfile_agree; [exact AG| | exact SEW]. intros a Ha. apply OWB. unfold stderr_addr, alloc_ceiling in *. lia. }
destruct (hglob_munch RHF RBR RND RBD c x g st m m' _ CX HG MU WM MI' ST' SEW') as [HG' _].
{ unfold hfoot_ok, HOUT_BYTES. apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia|]. apply Forall_cons; [left; cbn; lia| apply Forall_nil]. }
split. { exists j16, jsk, lk. split; [| exact LKOK]. eapply rw_cells_agree; [exact AG| exact LOW| intros a Ha; apply OWF; cbn in Ha; lia]. }
split; [exact C1|]. split; [exact C2|]. split; [exists stb'; exact STB'|].
split. { eapply (os_piece_agree2 _ _ _ _ _ _ AG OSP); [intros a Ha; apply OWF; lia|].
intros a (b & Hb & Ra). apply OWB. apply (HBLK b a); [| exact Ra].
unfold owned. unfold stream_blks in Hb. do 2 (apply in_app_iff; right).
apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [apply in_app_iff; left; exact Hb|].
apply in_app_iff in Hb. destruct Hb as [Hb|Hb]; [apply in_app_iff; right; apply in_app_iff; left; exact Hb|].
apply in_app_iff; right; apply in_app_iff; right; apply in_app_iff; left; exact Hb. }
split. { exists opj. eapply rw_cells_agree; [exact AG| exact OP| intros a Ha; apply OWF; cbn in Ha; lia]. }
split. { exists ogj. eapply rw_cells_agree; [exact AG| exact OG| intros a Ha; apply OWF; cbn in Ha; lia]. }
split. { eapply (sync_rep_agree _ _ _ _ _ _ _ AG SY); [intros a Ha; apply OWF; lia|].
intros a Ha. first [ sf_destruct 4%nat SY as _ _ DAT _ | sf_fb; destruct SY as (_ & _ & DAT & _) ]. unfold sync_data in DAT.
destruct (sy_data (h_oy g)) as [q|] eqn:ESD; [| first [ sf_destruct 4%nat DAT as _ _ _ ST0 | sf_fb; destruct DAT as (_ & _ & _ & ST0) ]; rewrite SYLEN, ST0 in Ha; lia].
apply OWB. apply (HBLK (q, a_D x, sy_storage (h_oy g)) a); [| cbn; rewrite <- SYLEN; lia].
unfold owned. rewrite ESD. do 5 (apply in_app_iff; right). left. reflexivity. }
split. { eapply (bits_rep_agree _ _ _ _ _ _ AG BI BOK); [intros a Ha; apply OWF; lia|].
intros a Ha. apply OWB. apply (HBLK (sb_chars (h_bits g), a_Dc x, sb_buf_size (h_bits g)) a); [| cbn; lia].
unfold owned. apply in_app_iff; right. apply in_app_iff; left. left. reflexivity. }
split. { exists pad. eapply rw_cells_agree; [exact AG| exact FSZ| intros a Ha; apply OWF; cbn in Ha; lia]. }
split; [exists outb'; split; [exact OUT'| exact LOUT']|].
split. { exists hij. eapply rw_cells_agree; [exact AG| exact HI| intros a Ha; apply OWF; cbn in Ha; lia]. }
split. { eapply rw_cells_agree; [exact AG| exact SAV| intros a Ha; apply OWF; cbn in Ha; lia]. }
split. { eapply (dec_piece_agree2 _ _ _ _ _ _ _ DRF AG DEC). intros a (b & Hb & Ra). apply OWB. apply (HBLK b a); [| exact Ra].
unfold owned. unfold dec_piece in DEC. destruct (h_st g); [| destruct DEC as [_ E]; rewrite E in Hb; destruct Hb].
apply in_app_iff; left. exact Hb. }
split; [exact HG'| exact PURE].
Qed.

Definition hclient_caller_addr (c : hcx) (a : Z) : Prop :=
usp c <= a \/ (0x3b000 <= a < 0x6e000 /\ ~ ralloc_static a /\ ~ (RSTDERR <= a < RSTDERR + 232)) \/ in_block (x_LB0 c) a.

Lemma hglob_agree2 {RCEIL : RunCeiling} : rheap_block_range_stmt -> forall (c : hcx) x h st m m' (P : Z -> Prop) errv',
hcx_ok c -> hglob c x h st m -> agree_on rsegs P m m' ->
RHEAP st (a_LB x) m' -> mem_inv rsegs m' -> stk rsegs m' (x_lo c) (hsp c) -> stderr_wfile m' ->
rw_cells rsegs m' RERRNO [C4 errv'] -> rauxv_ok m' (x_AB c) ->
(forall a, hclient_caller_addr c a -> P a) ->
hglob c x h st m'.
Proof.
intros RBR c x h st m m' P errv' CX HG AG HP1 MI1 ST1 SEW1 ERR1 AUX1 PC.
pose proof CX as sfP_; first [ sf_destruct 11%nat sfP_ as PF P0 P16 PL PIN SPAB ABB CEIL LO SP16 SPB | sf_fb; destruct sfP_ as (PF & P0 & P16 & PL & PIN & SPAB & ABB & CEIL & LO & SP16 & SPB) ].
pose proof HG as sfP_; first [ sf_destruct 11%nat sfP_ as HP PERM PAY TP SEW (errv & ERR) AUX MI ST PE SO | sf_fb; destruct sfP_ as (HP & PERM & PAY & TP & SEW & (errv & ERR) & AUX & MI & ST & PE & SO) ].
assert (HL0 : forall b, In b (x_LB0 c) -> In b (a_LB x)).
{ intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact PERM|]. apply in_app_iff. right. exact Hb. }
split; [exact HP1|]. split; [exact PERM|].
split. { eapply (pay_keep c _ _ _ CX AG PAY). intros NE IN a Ha. apply PC. right; right. exists (x_pb c, x_P c, zlength (x_payload c)). split; [exact IN| cbn; lia]. }
split. { eapply rtables_pristine_agree; [exact AG| | exact TP]. intros a Ha. apply PC. right; left.
unfold RTABLES_LO, RTABLES_HI, ralloc_static, RLIBC, RCTX, RERRNO, RSSP_GUARD, RGOT_SSP in *. lia. }
split; [exact SEW1|]. split; [exists errv'; exact ERR1|]. split; [exact AUX1|].
split; [exact MI1|]. split; [exact ST1|].
split. { eapply (pres_except_step RBR c _ _ _ _ _ _ CX HP); [exact HL0| exact PE| exact AG|].
intros a Hc Hout Hx. apply PC. destruct Hc as [Hc|[Hc|(bb & Hbb & Rbb)]].
- left. exact Hc.
- right; left. split; [lia|]. split; [tauto|]. intros Hs. apply Hx. cbn. left. cbn. exact Hs.
- right; right. exists bb. split; [exact Hbb| exact Rbb]. }
exact SO.
Qed.
