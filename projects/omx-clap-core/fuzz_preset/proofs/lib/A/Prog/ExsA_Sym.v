(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, ex_string's walk on image A' (#102 pin asan 1be0f53d96cb): the symbolic-state
   helpers the cut files share. The environments (atoms 0 .. 31 the registers, 32 .. 44 the thirteen words the prologue
   saved in es_saved's order, 45 .. the cut's extra atoms), the saved-word region of a state that reaches the epilogue,
   reading registers and regions back from a final state, and the callee-saved registers after the epilogue.
   PORTED from lib/B/Prog/ExsB_Sym.v (a Theorem Labs lane's B' walk): the same lemmas and tactics, image-free in content, at image
   A's listing (A_prog_listing, PI_prog_A) and segments; the prologue's saved-register layout es_saved is the same at
   A' (A 0x84038-0x84068: ra, s0 .. s11 at 136 .. 40(sp), frame 144). CHANGED: ES_REGS is A's ESB register clause
   (s2 = q + 8 in place of B's s1, s6 = in->end, s7 = the shadow base, s8 = q + 8's shadow address); the donor's pair
   lemma es_U_pair (B's operand order) is not here: ExsA_Hex2R.v states A's.
   Numerals: 32, 45 (DERIVED: atom numbering), 13 (COUNT: saved words), 40, 144 (LENGTH: the saved block in the frame). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04 YI00 YG0s YP07.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YI16 YG0p YCbqG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0d YP0c YC80 YPsym YC4aP YC1fP YC80x YC1fPx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YImgTop.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YO0b YO0c.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import ExsA_Stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope bv_scope.
Open Scope Z_scope.

#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).

(* ---- the saved-word region (read only, based at sp = the frame base), atoms 32 .. 44 ---- *)
Definition es_saved_regs : list (bv 5) := map (fun p => Z_to_bv 5 (snd p)) es_saved.
Definition es_chunk (j : nat) : YP09.chunk :=
  YP09.mkChunk (fst (nth j es_saved (0, 0))) (CVal 8 (SOff (32 + j) 0)).
Definition es_saved_chunks : list YP09.chunk := map es_chunk (seq 0 13).
Definition ES_SAVR : YP09.region := YP09.mkRegion (Some 2%nat) 40 144 0 0 es_saved_chunks.

(* YC1fP's prreg at image A's instance (as the donor's, ExvB_Exit.v exx_reg), and its form without prreg_norm *)
Ltac es_reg HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg (L := A_prog_listing) (PI := PI_prog_A) H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr; prreg_norm Hr
  end.
Ltac es_reg_st HS r Hr :=
  lazymatch type of HS with
  | st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
Ltac es_reg0 HS r Hr :=
  lazymatch type of HS with
  | st_ok_pi _ _ ?E ?ss (restrict ?H ?ms) =>
    pose proof (st_ok_pi_restrict_reg (L := A_prog_listing) (PI := PI_prog_A) H E ss ms r HS) as Hr;
    let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
    cbn [ms_regs restrict mkst] in Hr
  end.
(* the final environment of a run agrees with the start one below the token atoms (512 ..) *)
Ltac es_envkeep HS Ex EWf :=
  lazymatch type of HS with st_ok_pi _ _ ?Ef _ _ =>
    assert (EWf : forall n, (n < 512)%nat -> ew Ef n = ew Ex n)
      by (intros n Hn; repeat (rewrite ew_ewset_other by lia); reflexivity) end.

(* ESB's register clause: the registers every cut has *)
Definition ES_REGS : list (bv 5) := [2; 3; 4; 8; 18; 22; 23; 24; 25; 26; 27]%bv.
Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Definition es_xE (regs regs0 : bvmap 5 word) (extra : list word) : env :=
  @Eimg _ A_prog_listing PI_prog_A (Ereg regs (map (getr regs0) es_saved_regs ++ extra)).

Lemma es_xE_env : forall regs regs0 extra, img_env VAL A_LIM (es_xE regs regs0 extra).
Proof. intros regs regs0 extra. unfold es_xE. apply Eimg_env. Qed.
Lemma es_xE_low : forall regs regs0 extra n, (n < A_TEXT)%nat ->
  ew (es_xE regs regs0 extra) n = ew (Ereg regs (map (getr regs0) es_saved_regs ++ extra)) n.
Proof. intros regs regs0 extra n Hn. unfold es_xE. apply Eimg_low. exact Hn. Qed.
Lemma es_xE_reg : forall regs regs0 extra (r : bv 5) n, Z.of_nat n = bv_unsigned r ->
  ew (es_xE regs regs0 extra) n = getr regs r.
Proof.
intros regs regs0 extra r n Hn. pose proof (bv_unsigned_in_range 5 r) as R. change (bv_modulus 5) with 32 in R.
rewrite es_xE_low by (unfold A_TEXT; lia). apply ew_Ereg_nat. exact Hn.
Qed.
Lemma es_xE_saved : forall regs regs0 extra j, (j < 13)%nat ->
  ew (es_xE regs regs0 extra) (32 + j) = getr regs0 (Z_to_bv 5 (snd (nth j es_saved (0, 0)))).
Proof.
intros regs regs0 extra j Hj. rewrite es_xE_low by (unfold A_TEXT; lia). rewrite ew_Ereg_extra.
assert (HL : length (map (getr regs0) es_saved_regs) = 13%nat) by reflexivity.
rewrite app_nth1 by lia.
unfold es_saved_regs. rewrite map_map.
assert (HL2 : length es_saved = 13%nat) by reflexivity.
rewrite (nth_indep _ _ ((fun p : Z * Z => getr regs0 (Z_to_bv 5 (snd p))) (0, 0))) by (rewrite length_map; lia).
exact (map_nth (fun p : Z * Z => getr regs0 (Z_to_bv 5 (snd p))) es_saved (0, 0) j).
Qed.
Lemma es_xE_extra : forall regs regs0 extra j, (j < 100)%nat ->
  ew (es_xE regs regs0 extra) (45 + j) = nth j extra (Z_to_bv 64 0).
Proof.
intros regs regs0 extra j Hj. rewrite es_xE_low by (unfold A_TEXT; lia).
replace (45 + j)%nat with (32 + (13 + j))%nat by lia. rewrite ew_Ereg_extra.
assert (HL : length (map (getr regs0) es_saved_regs) = 13%nat) by reflexivity.
rewrite app_nth2 by lia. rewrite HL. f_equal. lia.
Qed.
(* the environment agrees with the cut's registers below atom 32 *)
Lemma es_xE_agree : forall regs regs0 extra, env_agree 32 (Ereg regs (map (getr regs0) es_saved_regs ++ extra))
  (es_xE regs regs0 extra).
Proof. intros regs regs0 extra. split; [intros m Hm; apply es_xE_low; unfold A_TEXT; lia | reflexivity]. Qed.
(* the engine's shadow tokens add atoms at 512 and up: agreement below 32 and the lower atoms are kept *)
Lemma es_agree_ewset : forall E0 E k w, (32 <= k)%nat -> env_agree 32 E0 E -> env_agree 32 E0 (ewset E k w).
Proof.
intros E0 E k w Hk [HA HD]. split; [intros n Hn; rewrite ew_ewset_other by lia; apply HA; exact Hn | exact HD].
Qed.

(* the saved-word region at a cut: ESB's frame clause *)
Lemma es_savr_ok : forall E (W : world rsegs) (regs : bvmap 5 word) memc extra,
  getr regs 2 = w64 (es_SP E) -> 0 <= es_SP E -> es_SP E + 144 <= 2 ^ 64 ->
  (forall o r, In (o, r) es_saved ->
     val_mem rsegs (rdW W memc) (es_SP E + o) 8 (bv_unsigned (getr (e_regs E) (Z_to_bv 5 r)))) ->
  region_ok rsegs (es_xE regs (e_regs E) extra) (rdW W memc) ES_SAVR.
Proof.
intros E W regs memc extra R2 H0 H1 HSAV.
assert (Usp : bv_unsigned (ew (es_xE regs (e_regs E) extra) 2) = es_SP E)
  by (rewrite (es_xE_reg regs (e_regs E) extra 2%bv 2) by reflexivity; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
remember (es_xE regs (e_regs E) extra) as Ex eqn:HEx.
unfold region_ok. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ES_SAVR].
rewrite Usp. split; [lia|]. split; [lia|]. split; [intros o Ho; exfalso; lia|].
unfold es_saved_chunks. apply Forall_forall. intros c Hc. apply in_map_iff in Hc as (j & <- & Hj).
apply in_seq in Hj. destruct Hj as [_ Hj]. cbn [Nat.add] in Hj.
destruct (nth j es_saved (0, 0)) as [o rr] eqn:Hor.
assert (Hin' : In (o, rr) es_saved) by (rewrite <- Hor; apply nth_In; cbn; lia).
unfold es_chunk. rewrite Hor. cbn [fst].
eapply (chunk_ok_val rsegs Ex _ (es_SP E) o 8 _ (bv_unsigned (getr (e_regs E) (Z_to_bv 5 rr)))).
- cbn [sv_denot]. rewrite HEx, (es_xE_saved regs (e_regs E) extra j Hj), Hor. cbn [snd].
  rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (u64_range (getr (e_regs E) (Z_to_bv 5 rr))). cbn. lia.
- cbn. lia.
- exact (HSAV o rr Hin').
Qed.

(* the callee-saved registers after the epilogue: sp, gp, tp, and each saved word reloaded *)
Lemma es_exit_aregs : forall (regs0 regs' : bvmap 5 word),
  getr regs' (Z_to_bv 5 2) = getr regs0 (Z_to_bv 5 2) -> getr regs' (Z_to_bv 5 3) = getr regs0 (Z_to_bv 5 3) ->
  getr regs' (Z_to_bv 5 4) = getr regs0 (Z_to_bv 5 4) ->
  (forall j, (1 <= j < 13)%nat ->
     getr regs' (Z_to_bv 5 (snd (nth j es_saved (0, 0)))) = getr regs0 (Z_to_bv 5 (snd (nth j es_saved (0, 0))))) ->
  aregs_preserved regs0 regs'.
Proof.
intros regs0 regs' H2 H3 H4 HS rr Hrr. unfold acallee_saved in Hrr.
assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
  rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
first [ exact H2 | exact H3 | exact H4
      | exact (HS 1%nat ltac:(lia)) | exact (HS 2%nat ltac:(lia)) | exact (HS 3%nat ltac:(lia))
      | exact (HS 4%nat ltac:(lia)) | exact (HS 5%nat ltac:(lia)) | exact (HS 6%nat ltac:(lia))
      | exact (HS 7%nat ltac:(lia)) | exact (HS 8%nat ltac:(lia)) | exact (HS 9%nat ltac:(lia))
      | exact (HS 10%nat ltac:(lia)) | exact (HS 11%nat ltac:(lia)) | exact (HS 12%nat ltac:(lia)) ].
Qed.

(* denotations of atoms with a constant *)
Lemma es_den_off : forall E n c z, ew E n = Z_to_bv 64 z -> 0 <= z < 2 ^ 64 -> 0 <= z + c < 2 ^ 64 ->
  sv_denot E (SOff n c) = Z_to_bv 64 (z + c).
Proof.
intros E n c z H Hz Hzc. rewrite denot_lit_U. f_equal. rewrite U_SOff, H, unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma es_den0 : forall E n, sv_denot E (SOff n 0) = ew E n.
Proof.
intros E n. rewrite denot_lit_U, U_SOff, Z.add_0_r, zcanon_id by (pose proof (u64_range (ew E n)); unfold M64; lia).
apply Z_to_bv_bv_unsigned.
Qed.
(* a region of a final symbolic state, read back (ExvB_Exit.v exx_region_nth / exx_field) *)
Lemma es_region_nth : forall E ss ms i rg,
  st_ok_pi rsegs VAL E ss ms -> nth_error (ss_mem ss) i = Some rg -> region_ok rsegs E (ms_mem ms) rg.
Proof.
intros E ss ms i rg HS Hi. unfold st_ok_pi in HS. destruct (st_ok_mem_ok rsegs E _ ms HS) as (_ & Hrs & _).
destruct ss. exact (proj1 (Forall_forall _ _) Hrs rg (nth_error_In _ _ Hi)).
Qed.
Lemma es_field : forall E m n b cs lo hi wlo whi od (w : N) e v,
  region_ok rsegs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> In (YP09.mkChunk od (CVal w e)) cs -> sv_denot E e = Z_to_bv 64 v ->
  0 <= v < 2 ^ (8 * Z.of_N w) -> (Z.of_N w <= 8) ->
  val_mem rsegs m (b + od) (N.to_nat w) v.
Proof.
intros E m n b cs lo hi wlo whi od w e v (_ & _ & _ & Hcs) Hn Hc He Hv Hw.
pose proof (proj1 (Forall_forall _ _) Hcs _ Hc) as Hck. cbn [YP09.r_base base_val] in Hck. rewrite Hn in Hck.
exact (val_of_chunk_ok rsegs E m b od w e v Hck He Hv Hw).
Qed.
(* an atom plus a constant, through an environment that agrees below the token atoms *)
Lemma es_U_off : forall Ef Ex n c v, (forall m, (m < 512)%nat -> ew Ef m = ew Ex m) -> (n < 512)%nat ->
  ew Ex n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 -> U Ef (SOff n c) = v + c.
Proof.
intros Ef Ex n c v EW Hn H Hv Hvc. rewrite U_SOff, (EW n Hn), H, unsigned_lit_small by lia.
apply zcanon_id. unfold M64. lia.
Qed.
Lemma es_U_lit : forall E z, 0 <= z < 2 ^ 64 -> U E (SLit z) = z.
Proof. intros E z Hz. unfold U. cbn [sv_denot]. apply unsigned_lit_small. exact Hz. Qed.
(* the signed branches at small operands *)
Lemma es_branch_lt_U : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (U E a <? U E b).
Proof.
intros E a b Ha Hb. rewrite YO0c.branch_lt. fold (U E a) (U E b).
pose proof (U_range E a). pose proof (U_range E b). rewrite !YO0b.s64_small by (unfold M64 in *; lia). reflexivity.
Qed.
Lemma es_branch_ge_U : forall E a b, U E a < 2 ^ 63 -> U E b < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (U E a <? U E b).
Proof.
intros E a b Ha Hb. rewrite YO0c.branch_ge. fold (U E a) (U E b).
pose proof (U_range E a). pose proof (U_range E b). rewrite !YO0b.s64_small by (unfold M64 in *; lia). reflexivity.
Qed.

(* the bytes a run kept: outside its writable windows (ex_ws_x.v exw_kept, restated) *)
Lemma es_kept : forall E rs H (m m' : word -> option byte) (Zs : Z -> Prop),
  frame_of E rs (mrestrict H m) (mrestrict H m') ->
  (forall b wlo whi a, In (b, wlo, whi) (windows rs) -> base_val E b + wlo <= a < base_val E b + whi -> Zs a) ->
  forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview rsegs H m' a = aview rsegs H m a.
Proof.
intros E rs H m m' Zs HFR Hw a Ha Hn. apply (aview_eq_of rsegs). apply HFR. rewrite unsigned_lit_small by lia.
intros Hin. destruct (in_wrange_windows E rs a Hin) as (b & wlo & whi & Hi & Hr). exact (Hn (Hw b wlo whi a Hi Hr)).
Qed.
(* the write premise region by region (ex_ws_x.v exw_awr_cons, restated) *)
Lemma es_awr_cons : forall E r rs STK sp0 FP bl0 blc ly own,
  (forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
     awr_byte STK sp0 FP bl0 blc ly own a) ->
  awr_ok E rs STK sp0 FP bl0 blc ly own -> awr_ok E (r :: rs) STK sp0 FP bl0 blc ly own.
Proof. intros E r rs STK sp0 FP bl0 blc ly own Hw H a (r' & [<-|Hin] & Ha); [exact (Hw a Ha) | apply H; exists r'; auto]. Qed.
(* a list of registers pinned to literals in the symbolic register file *)
Definition es_pin_sr (l : list (bv 5 * Z)) (sr : list sv) : list sv :=
  fold_left (fun s rz => sr_set s (fst rz) (SLit (snd rz))) l sr.
Lemma es_regs_ok_pins : forall E l sr regs, regs_ok E sr regs ->
  Forall (fun rz => fst rz <> 0%bv /\ getr regs (fst rz) = Z_to_bv 64 (snd rz)) l ->
  regs_ok E (es_pin_sr l sr) regs.
Proof.
intros E l. induction l as [|[r z] l IH]; intros sr regs HR HF; [exact HR|].
inversion HF as [|x l' [Hr0 Hv] HF' Hx]; subst. cbn [es_pin_sr fold_left fst snd].
apply (IH _ regs); [|exact HF']. apply regs_ok_pin; [exact HR | exact Hr0 | exact Hv].
Qed.

(* the shadow of a range, along equal views of the shadow bytes (ex_ws_x.v exw_ra_kept, restated) *)
Lemma es_ra_kept : forall H (m m' : word -> option byte) a n,
  (forall x, a <= x < a + n -> aview rsegs H m' (shadow_of_addr SHADOW_OFF x) = aview rsegs H m (shadow_of_addr SHADOW_OFF x)) ->
  range_addressable (aview rsegs H m) SHADOW_OFF a n -> range_addressable (aview rsegs H m') SHADOW_OFF a n.
Proof. intros H m m' a n HE HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. rewrite (HE x Hx). auto. Qed.

(* aregs_preserved from the callee-saved registers kept one by one *)
Definition ES_CS : list (bv 5) := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Lemma es_aregs_of_kept : forall (regs regs' : bvmap 5 word),
  (forall r, In r ES_CS -> getr regs' r = getr regs r) -> aregs_preserved regs regs'.
Proof.
intros regs regs' HK rr Hrr. unfold acallee_saved in Hrr. apply HK.
assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/ rr = 22 \/
  rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
unfold ES_CS. cbn [In].
destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]]];
  repeat (first [left; apply bv_eq; reflexivity | right]).
Qed.
(* callee-saved registers of a list, across a callee *)
Lemma es_aregs_l : forall (l : list (bv 5)) (regs regs' : bvmap 5 word),
  forallb (fun r : bv 5 => (bv_unsigned r =? 2) || (bv_unsigned r =? 3) || (bv_unsigned r =? 4) ||
    (bv_unsigned r =? 8) || (bv_unsigned r =? 9) || ((18 <=? bv_unsigned r) && (bv_unsigned r <=? 27))) l = true ->
  aregs_preserved regs regs' -> forall r, In r l -> getr regs' r = getr regs r.
Proof.
intros l regs regs' Hb HA r Hr. rewrite forallb_forall in Hb. specialize (Hb r Hr).
assert (Hcs : acallee_saved (bv_unsigned r)).
{ unfold acallee_saved. rewrite !Bool.orb_true_iff, Bool.andb_true_iff, !Z.eqb_eq, !Z.leb_le in Hb. lia. }
pose proof (HA (bv_unsigned r) Hcs) as H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.
(* ESB's registers across a callee: all callee-saved *)
Lemma es_aregs_ES : forall (regs regs' : bvmap 5 word), aregs_preserved regs regs' ->
  forall r, In r ES_REGS -> getr regs' r = getr regs r.
Proof.
intros regs regs' HA r Hr.
assert (Hb : forallb (fun r : bv 5 => (bv_unsigned r =? 2) || (bv_unsigned r =? 3) || (bv_unsigned r =? 4) ||
  (bv_unsigned r =? 8) || (bv_unsigned r =? 9) || ((18 <=? bv_unsigned r) && (bv_unsigned r <=? 27))) ES_REGS = true)
  by (vm_compute; reflexivity).
rewrite forallb_forall in Hb. specialize (Hb r Hr).
assert (Hcs : acallee_saved (bv_unsigned r)).
{ unfold acallee_saved. rewrite !Bool.orb_true_iff, Bool.andb_true_iff, !Z.eqb_eq, !Z.leb_le in Hb. lia. }
pose proof (HA (bv_unsigned r) Hcs) as H. rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* registers the state pins to literals, read back *)
Lemma es_pins_kept : forall E ss ms (regs : bvmap 5 word) (H : word -> bool) (l : list (bv 5 * Z)),
  st_ok_pi rsegs VAL E ss (restrict H ms) ->
  Forall (fun rz => sr_get (ss_regs ss) (fst rz) = SLit (snd rz)) l ->
  Forall (fun rz => getr regs (fst rz) = Z_to_bv 64 (snd rz)) l ->
  forall r, In r (map fst l) -> getr (ms_regs ms) r = getr regs r.
Proof.
intros E ss ms regs H l HS HP HR r Hr. apply in_map_iff in Hr as ([r' z] & <- & Hin). cbn [fst].
pose proof (proj1 (Forall_forall _ _) HP _ Hin) as P1. pose proof (proj1 (Forall_forall _ _) HR _ Hin) as R1.
cbn [fst snd] in P1, R1. rewrite (st_ok_pi_restrict_reg (L := A_prog_listing) (PI := PI_prog_A) H E ss ms r' HS), P1, R1.
reflexivity.
Qed.

(* ESB's registers kept, from a kept list K (regs_kept_of_st_ok_pi) and a few registers X proved by hand *)
Lemma es_regs_of : forall (regs regs' : bvmap 5 word) (K X : list (bv 5)),
  (forall r, In r K -> getr regs' r = getr regs r) -> (forall r, In r X -> getr regs' r = getr regs r) ->
  forallb (fun r => existsb (fun k => Z.eqb (bv_unsigned r) (bv_unsigned k)) (K ++ X)) ES_REGS = true ->
  forall r, In r ES_REGS -> getr regs' r = getr regs r.
Proof.
intros regs regs' K X HK HX Hb r Hr. rewrite forallb_forall in Hb. specialize (Hb r Hr).
apply existsb_exists in Hb as (k & Hk & Hkb). apply Z.eqb_eq in Hkb. assert (r = k) as -> by (apply bv_eq; exact Hkb).
apply in_app_or in Hk as [Hk|Hk]; [exact (HK k Hk) | exact (HX k Hk)].
Qed.

Lemma es_branch_ge_vals : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_GE (sv_denot E a) (sv_denot E b) = negb (x <? y).
Proof. intros E a b x y Ha Hb Hx Hy. rewrite es_branch_ge_U by lia. rewrite Ha, Hb. reflexivity. Qed.
Lemma es_branch_lt_vals : forall E a b x y, U E a = x -> U E b = y -> 0 <= x < 2 ^ 63 -> 0 <= y < 2 ^ 63 ->
  branch_taken BC_LT (sv_denot E a) (sv_denot E b) = (x <? y).
Proof. intros E a b x y Ha Hb Hx Hy. rewrite es_branch_lt_U by lia. rewrite Ha, Hb. reflexivity. Qed.

(* a - b as the engine writes sub (YE2i.v U_sub_form_gen, restated) *)
Lemma es_U_sub : forall E a b, U E b <= U E a -> U E (SAlu ALU_ADD a (SMd M_MUL b (SLit (-1)))) = U E a - U E b.
Proof.
intros E a b Hle. pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb. unfold M64 in *.
rewrite U_SAlu, U_SMd, U_SLit. cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
rewrite Zplus_mod_idemp_r.
replace (U E a + U E b * (2 ^ 64 - 1)) with (U E a - U E b + U E b * 2 ^ 64) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* andi x,-1024 of a value below 2 ^ 16: the value without its low 10 bits *)
Lemma es_U_andm : forall E a h, U E a = h -> 0 <= h < 65536 ->
  U E (SAlu ALU_AND a (SLit (-1024))) = h - h mod 1024.
Proof.
intros E a h Ha Hh. rewrite U_SAlu, Ha, U_SLit.
assert (A : forallb (fun y => Z.eqb (zcanon (zalu_raw 63 64 ALU_AND y (zcanon (-1024)))) (y - y mod 1024))
  (map Z.of_nat (seq 0 65536)) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in A. apply Z.eqb_eq, A. apply in_map_iff. exists (Z.to_nat h).
split; [apply Z2Nat.id; apply Hh|]. apply in_seq. split; [apply Nat.le_0_l|].
apply Nat2Z.inj_lt. rewrite Z2Nat.id by apply Hh. exact (proj2 Hh).
Qed.

Lemma es_U_sub_r : forall E a b, U E b <= U E a -> U E (SAlu ALU_ADD (SMd M_MUL b (SLit (-1))) a) = U E a - U E b.
Proof.
intros E a b Hle. rewrite <- (es_U_sub E a b Hle). rewrite !U_SAlu. cbn [zalu_raw]. rewrite Z.add_comm. reflexivity.
Qed.

(* the shadow address of an atom plus an offset *)
Lemma es_denot_shx_off : forall E n m c v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb ->
  0 <= v < 2 ^ 63 -> 0 <= v + c < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + (v + c) / 8).
Proof.
intros E n m c v sb Hn Hm Hv Hvc Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n c) (SLit 3)) (SOff m 0)) = sb + (v + c) / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia.
rewrite Z.add_0_r.
rewrite (zcanon_id (v + c)) by (unfold M64; lia).
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos (v + c) 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound (v + c) 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id ((v + c) / 8)) by (unfold M64; lia). rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* the shadow address of an atom, as the engine's shadow token reads it (ex_ws_x.v exw_denot_shx, restated) *)
Lemma es_denot_shx : forall E n m v sb, ew E n = Z_to_bv 64 v -> ew E m = Z_to_bv 64 sb -> 0 <= v < 2 ^ 63 -> 0 <= sb < 2 ^ 32 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = Z_to_bv 64 (sb + v / 8).
Proof.
intros E n m v sb Hn Hm Hv Hsb.
rewrite <- (Z_to_bv_bv_unsigned 64 (sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)))). f_equal.
change (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff n 0) (SLit 3)) (SOff m 0)) = sb + v / 8).
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite !U_SOff, Hn, Hm. rewrite !unsigned_lit_small by lia.
rewrite !Z.add_0_r.
change (Z.land (U E (SLit 3)) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos v 8 ltac:(lia) ltac:(lia)). pose proof (Z.div_lt_upper_bound v 8 (2 ^ 60) ltac:(lia) ltac:(lia)).
rewrite (zcanon_id v) by (unfold M64; lia). rewrite (zcanon_id (v / 8)) by (unfold M64; lia).
rewrite (zcanon_id sb) by (unfold M64; lia).
rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
End c.
(* env_agree 32 (Ereg regs ..) at a final environment, from the start one es_xE (HEx : Ex = es_xE ..) *)
(* the write premise, region by region: read-only regions by lia, the others by tac a Ha *)
Ltac es_awr tac :=
  lazymatch goal with |- awr_ok ?Ex ?rs _ _ _ _ _ _ _ =>
    let rs' := eval vm_compute in rs in change rs with rs' end;
  repeat (apply es_awr_cons; [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val];
    let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
    cbn [ew ewset Nat.eqb] in Ha; first [ lia | tac a Ha ] | ]);
  apply awr_ok_nil.
(* the KEPT clause of a run (ex_ws_x.v exw_kept_of, restated) *)
Ltac es_kept_of HFr Zs ev :=
  lazymatch type of HFr with frame_of ?E ?rs (mrestrict ?H ?m) (mrestrict _ ?m') =>
  let KP := fresh "KEPT" in
  assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ Zs a -> aview rsegs H m' a = aview rsegs H m a);
  [ apply (es_kept E rs H m m' Zs HFr); intros b_ wlo_ whi_ a0_ Hin_ Hrr_; vm_compute in Hin_;
    repeat (destruct Hin_ as [Hq_ | Hin_]; [injection Hq_ as <- <- <-; cbn [base_val] in Hrr_; ev Hrr_; cbv beta; lia|]);
    destruct Hin_
  | cbv beta in KP ]
  end.
(* a branch condition with atoms / literals, to Z *)
Ltac es_Uhc Hc EWf :=
  repeat (rewrite ?branch_eq_U, ?branch_ne_U, ?branch_ltu_U, ?branch_geu_U in Hc);
  repeat match type of Hc with context [U ?Ef (SOff ?n ?c)] =>
    match goal with Hn : ew ?Ex0 n = Z_to_bv 64 ?v |- _ =>
      rewrite (es_U_off Ef Ex0 n c v EWf ltac:(lia) Hn ltac:(lia) ltac:(lia)) in Hc end end;
  repeat match type of Hc with context [U ?Ef (SLit ?z)] => rewrite (es_U_lit Ef z ltac:(lia)) in Hc end;
  rewrite ?Z.add_0_r in Hc.
Ltac es_agree_tac HEx := repeat (apply es_agree_ewset; [lia|]); rewrite HEx; apply es_xE_agree.
(* the registers a leaf keeps: the atoms of KL (regs_kept_of_st_ok_pi) and the pinned literals of PINS; HR is ESB's
   register clause at the leaf's final machine state *)
Ltac es_leaf_regs HS HEx regs KL PINS HPN HR :=
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msF) =>
    let HKR := fresh "HKR" in
    pose proof (regs_kept_of_st_ok_pi (L := A_prog_listing) (PI := PI_prog_A) _ _ _ regs _ KL HS
      ltac:(es_agree_tac HEx) ltac:(vm_compute; reflexivity)) as HKR; cbn [ms_regs restrict] in HKR;
    let HPK := fresh "HPK" in
    pose proof (es_pins_kept _ _ msF regs _ PINS HS
      ltac:(repeat (apply Forall_cons; [vm_compute; reflexivity|]); apply Forall_nil) HPN) as HPK;
    assert (HR : forall r, In r ES_REGS -> getr (ms_regs msF) r = getr regs r)
      by exact (es_regs_of regs (ms_regs msF) KL (map fst PINS) HKR HPK ltac:(vm_compute; reflexivity))
  end.
(* the goal's pc, as a run leaves it, written as es_pc off (ExvB_Disp_str.v exvs_pc_to) *)
Ltac es_pc_to off :=
  lazymatch goal with |- SRr _ _ {| cfg_ms := YK11.mkst _ (Z_to_bv 64 ?pc) _ _; cfg_model := _ |} _ =>
    replace pc with (es_pc off) by (vm_compute; reflexivity) end.
