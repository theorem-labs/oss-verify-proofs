(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module names changed; 767 of its 798 lines of code are new or changed and 38 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YG0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YI04 YI09 YI08 YI00 YN3v YG0v YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d YCbp YE00 YE01 YO09 YI16 YM05 YImgTop.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
PaTable PaSym PaShadow PaRun PaStep PaJournal DiscoSyms DiscoList DiscoAddr DiscoPa DiscoPaLib DiscoBase DiscoFrame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
YC1g YC1h YC81 YC4b YC45 YC85 YCkd YC1i ACbf ACj1 DiscoACjr DiscoACja.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import
DiscoEntryInv DiscoEntSeatStmt DiscoEntSeat DiscoEntBodyStmt DiscoEntBody DiscoEntObsCuts.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_classify_c hunt_c SightModel slot_inv slot_frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require reac_disco_table_observe_c slot_observe disco_table.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Bytes.
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

Lemma o4_ble_byte : forall (bs : list byte) n k, length bs = n -> (k < n)%nat ->
  Z.shiftr (bytes_le_to_Z bs mod 2 ^ (8 * Z.of_nat n)) (8 * Z.of_nat k) mod 256 = bv_unsigned (nth k bs (Z_to_bv 8 0)).
Proof.
intros bs n k <-. revert k. induction bs as [|b bs IH]; intros k Hk; [cbn in Hk; lia|].
rewrite (Z.mod_small (bytes_le_to_Z (b :: bs))) by exact (disco_table.ble_range (b :: bs)).
pose proof (bv_unsigned_in_range _ b) as Hb. change (bv_modulus 8) with 256 in Hb.
pose proof (disco_table.ble_range bs) as Hr.
assert (Ec : bytes_le_to_Z (b :: bs) = bv_unsigned b + bytes_le_to_Z bs * 256)
  by (rewrite !Bytes.bytes_le_to_Z_le_val; cbn [map Bytes.le_val]; lia).
rewrite Ec. destruct k as [|k].
- cbn [nth]. rewrite Z.mul_0_r, Z.shiftr_0_r. rewrite Z_mod_plus_full. apply Z.mod_small. lia.
- cbn [nth length] in Hk |- *. rewrite Z.shiftr_div_pow2 by lia.
  replace (8 * Z.of_nat (S k)) with (8 + 8 * Z.of_nat k) by lia. rewrite Z.pow_add_r by lia.
  rewrite <- Z.div_div by (try apply Z.pow_nonzero; lia).
  change (2 ^ 8) with 256. rewrite Z.div_add by lia. rewrite (Z.div_small (bv_unsigned b) 256) by lia. rewrite Z.add_0_l.
  specialize (IH k ltac:(lia)). rewrite (Z.mod_small (bytes_le_to_Z bs)) in IH by exact Hr.
  rewrite Z.shiftr_div_pow2 in IH by lia. exact IH.
Qed.
Lemma o4_obs_len : forall regs, length (obs_vals regs) = 32%nat.
Proof. intros regs. unfold obs_vals. rewrite length_map, length_seq. reflexivity. Qed.
Lemma o4_sub_len : forall (L : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) -> length (sub L k n) = n.
Proof. intros L k n Hk Hn. unfold sub. rewrite length_firstn, length_skipn. lia. Qed.
Lemma o4_u_range : forall (L : list byte) k n, 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  0 <= u_at L k n < 2 ^ (8 * Z.of_nat n).
Proof.
intros L k n Hk Hn. unfold u_at. pose proof (disco_table.ble_range (sub L k n)) as H.
rewrite (o4_sub_len L k n Hk Hn) in H. exact H.
Qed.
Lemma o4_nth_sub : forall (L : list byte) k n j d, 0 <= k -> (j < n)%nat -> nth j (sub L k n) d = nth (Z.to_nat k + j) L d.
Proof.
intros L k n j d Hk Hj. unfold sub. rewrite nth_firstn. replace (j <? n)%nat with true by (symmetry; apply Nat.ltb_lt; exact Hj).
rewrite nth_skipn. reflexivity.
Qed.
Lemma o4_u_le : forall z (n : nat), 0 <= z < 2 ^ (8 * Z.of_nat n) -> bytes_le_to_Z (Z_to_le_bytes n z) = z.
Proof. intros z n Hz. rewrite bytes_le_to_Z_of_le_bytes by lia. apply Z.mod_small. exact Hz. Qed.
Lemma o4_mod_nz : forall x, x <> 0 -> - 2 ^ 31 <= x < 2 ^ 31 -> x mod 2 ^ 64 <> 0 mod 2 ^ 64.
Proof. intros x Hx Hr. rewrite Z.mod_0_l by lia. destruct (Z_lt_le_dec x 0); [rewrite Z.mod_eq by lia | rewrite Z.mod_small by lia]; lia. Qed.
Lemma o4_pres : forall a b (r : bv 5), aregs_preserved a b -> acallee_saved (bv_unsigned r) -> getr b r = getr a r.
Proof. intros a b r H Hr. pose proof (H (bv_unsigned r) Hr) as E. rewrite Z_to_bv_bv_unsigned in E. exact E. Qed.

Ltac o4_rr H := lazymatch type of H with _ = sv_denot _ (sr_get ?sr ?r) =>
  let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v in H end.
Ltac o4_upd :=
  lazymatch goal with HF : frame_of _ _ ?m1 ?m2, MP : forall x, ?m1 x = ?m0 x |- _ =>
    let MP2 := fresh "MP" in
    assert (MP2 : forall x, m2 x = m0 x)
      by (intros x; rewrite (frame_of_ro_pt _ _ _ _ HF ltac:(vm_compute; reflexivity) x); apply MP);
    clear MP; rename MP2 into MP end;
  repeat match goal with H : frame_of _ _ _ _ |- _ => clear H | H : mem_grows _ _ |- _ => clear H end.
Ltac o4_cs := unfold acallee_saved;
  repeat match goal with |- context [bv_unsigned ?x] => let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v end; lia.
Ltac o4_awr := cbn [ss_mem]; repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil.
Ltac o4_run RUN :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_tok RUN HS HJ SHOK OBspan; [o4_awr | o4_upd] end.
Ltac o4_runto RUNTO stop :=
  lazymatch goal with HS : st_ok_pi _ _ _ _ _, HJ : ajournal _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _, SHOK : sh_ok _ _ _ _ _ |- _ =>
    paj_run_to_tok RUNTO HS HJ SHOK OBspan stop; [o4_awr | o4_upd] end.

Section u.
Variable E : env.
Lemma o4_sv_atom : forall q v, ew E q = Z_to_bv 64 v -> sv_denot E (SOff q 0) = Z_to_bv 64 v.
Proof. intros q v H. cbn [sv_denot]. rewrite H, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity. Qed.
Lemma o4_ew_of_sv : forall q w, sv_denot E (SOff q 0) = w -> ew E q = w.
Proof. intros q w H. cbn [sv_denot] in H. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma o4_sv_sext32 : forall q u, ew E q = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  sv_denot E (SExt true 32 (SOff q 0)) = Z_to_bv 64 (bv_swrap 32 u).
Proof.
intros q u H Hu. rewrite denot_lit_U, U_SExt, U_SOff, H. rewrite (Z_to_bv_unsigned 64 u).
unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite (Z.mod_small u) by lia. rewrite Z.add_0_r.
rewrite (zcanon_id u) by (unfold M64; lia). change (2 ^ Z.of_N 32) with (2 ^ 32). rewrite (Z.mod_small u) by lia.
rewrite zcanon_wrap. apply bv_eq. rewrite !Z_to_bv_unsigned. apply bv_wrap_bv_wrap. lia.
Qed.
Lemma o4_br_ne_false : forall a b, sv_denot E a = sv_denot E b -> branch_taken BC_NE (sv_denot E a) (sv_denot E b) = false.
Proof. intros a b H. rewrite branch_ne_U. unfold U. rewrite H, Z.eqb_refl. reflexivity. Qed.
Lemma o4_br_eq_false : forall a b x y, sv_denot E a = Z_to_bv 64 x -> sv_denot E b = Z_to_bv 64 y ->
  x mod 2 ^ 64 <> y mod 2 ^ 64 -> branch_taken BC_EQ (sv_denot E a) (sv_denot E b) = false.
Proof.
intros a b x y Ha Hb Hxy. rewrite branch_eq_U. unfold U. rewrite Ha, Hb, !Z_to_bv_unsigned. unfold bv_wrap.
change (bv_modulus 64) with (2 ^ 64). apply Z.eqb_neq. exact Hxy.
Qed.
Lemma o4_br_lt7 : forall v, ew E 550 = Z_to_bv 64 v -> 0 <= v <= 8 ->
  branch_taken BC_LT (sv_denot E (SLit 7)) (sv_denot E (SOff 550 0)) = (7 <? v).
Proof.
intros v H Hv. rewrite (o4_sv_atom 550 v H).
assert (v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7 \/ v = 8) as Hc by lia.
repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]). subst v. vm_compute. reflexivity.
Qed.
Lemma o4_sv_aluw1 : forall v, ew E 550 = Z_to_bv 64 v -> 0 <= v < 8 ->
  sv_denot E (SAluw ALU_ADD (SOff 550 0) (SLit 1)) = Z_to_bv 64 (v + 1).
Proof.
intros v H Hv. cbn [sv_denot]. rewrite H.
assert (v = 0 \/ v = 1 \/ v = 2 \/ v = 3 \/ v = 4 \/ v = 5 \/ v = 6 \/ v = 7) as Hc by lia.
repeat (destruct Hc as [->|Hc]; [vm_compute; reflexivity|]). subst v. vm_compute. reflexivity.
Qed.
Lemma o4_sv_addr : forall fb c v, ew E 516 = Z_to_bv 64 fb -> ew E 550 = Z_to_bv 64 v ->
  sv_denot E (SAlu ALU_ADD (SOff 516 c) (SMd M_MUL (SOff 550 0) (SLit 48))) = Z_to_bv 64 (fb + c + 48 * v).
Proof.
intros fb c v Hf Hv. rewrite denot_lit_U. rewrite U_SAlu, U_SMd, !U_SOff, U_SLit, Hf, Hv.
cbn [zalu_raw zmd_raw]. apply bv_eq. rewrite !Z_to_bv_unsigned.
unfold zcanon, bv_wrap. change (bv_modulus 64) with 18446744073709551616. rewrite Z.add_0_r.
change (48 mod 18446744073709551616) with 48.
rewrite (Zmod_mod v), Z.mul_mod_idemp_l, Z.add_mod_idemp_r, Z.add_mod_idemp_l, Zmod_mod by discriminate.
change (48 mod M64) with 48. rewrite <- Z.add_assoc, Z.add_mod_idemp_l by discriminate. f_equal. lia.
Qed.
End u.

Definition o4_fcs (e : Z) : list YP09.chunk :=
  [YP09.mkChunk (e + 8) (CVal 4 (SOff 563 0)); YP09.mkChunk (e + 12) (CVal 1 (SOff 564 0));
   YP09.mkChunk (e + 13) (CVal 1 (SOff 565 0)); YP09.mkChunk (e + 14) (CVal 1 (SOff 566 0));
   YP09.mkChunk (e + 15) (CVal 1 (SOff 567 0)); YP09.mkChunk (e + 16) (CVal 1 (SOff 568 0));
   YP09.mkChunk (e + 20) (CVal 4 (SOff 569 0)); YP09.mkChunk (e + 24) (CVal 4 (SOff 570 0));
   YP09.mkChunk (e + 32) (CVal 8 (SOff 571 0)); YP09.mkChunk (e + 40) (CVal 8 (SOff 571 0));
   YP09.mkChunk 3000 (CVal 4 (SOff 563 0)); YP09.mkChunk 3004 (CVal 1 (SOff 564 0));
   YP09.mkChunk 3005 (CVal 1 (SOff 565 0)); YP09.mkChunk 3006 (CVal 1 (SOff 566 0));
   YP09.mkChunk 3007 (CVal 1 (SOff 567 0)); YP09.mkChunk 3008 (CVal 1 (SOff 568 0));
   YP09.mkChunk 3012 (CVal 4 (SOff 569 0))].
Definition o4_acs : list YP09.chunk :=
  [YP09.mkChunk 248 (CVal 8 (SOff 572 0)); YP09.mkChunk 344 (CVal 8 (SOff 571 0)); YP09.mkChunk 408 (CVal 8 (SOff 570 0))].
Lemma o4_w64_mod : forall x, Z_to_bv 64 x = Z_to_bv 64 (x mod 2 ^ 64).
Proof. intros x. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Zmod_mod. reflexivity. Qed.

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
Context {RO : ro_below_ofl SEGS pa_relro_lo pa_relro_hi}.

Lemma o4_val_mem_sub : forall (m : word -> option byte) p (L : list byte) k (n : nat),
  garr8 SEGS m p (map (fun b : byte => bv_unsigned b) L) -> 0 <= k -> k + Z.of_nat n <= Z.of_nat (length L) ->
  val_mem SEGS m (p + k) n (u_at L k n).
Proof.
intros m p L k n HG Hk Hn j Hj.
unfold u_at, YO0f.le_byte. rewrite (o4_ble_byte (sub L k n) n j (o4_sub_len L k n Hk Hn) Hj).
rewrite (o4_nth_sub L k n j _ Hk Hj).
replace (p + k + Z.of_nat j) with (p + Z.of_nat (Z.to_nat k + j)) by lia.
rewrite (YI00.garr8_mbyte SEGS m p _ (Z.to_nat k + j) HG) by (rewrite length_map; lia).
f_equal. rewrite (map_nth (fun b : byte => bv_unsigned b) L (Z_to_bv 8 0)). rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma o4_aview_garr8 : forall H (m : word -> option byte) p (L : list byte) j,
  garr8 SEGS (mrestrict H m) p (map (fun b : byte => bv_unsigned b) L) -> (j < length L)%nat ->
  aview SEGS H m (p + Z.of_nat j) = Some (bv_unsigned (nth j L (Z_to_bv 8 0))).
Proof.
intros H m p L j HG Hj. unfold aview.
rewrite (YI00.garr8_mbyte SEGS (mrestrict H m) p _ j HG) by (rewrite length_map; exact Hj).
cbn [option_map]. f_equal. rewrite (map_nth (fun b : byte => bv_unsigned b) L (Z_to_bv 8 0)).
rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.
Lemma o4_ew_app : forall cx E regs xs k, (k < 563)%nat ->
  ew (d_env cx E (obs_vals regs ++ xs)) k = ew (d_env cx E (obs_vals regs)) k.
Proof.
intros cx E regs xs k Hk. unfold d_env, havoc. cbn [ew].
destruct (k <? AT_FL)%nat eqn:Hl; [reflexivity|]. apply Nat.ltb_ge in Hl. unfold AT_FL in *.
rewrite app_comm_cons. rewrite app_nth1; [reflexivity|]. cbn [length]. rewrite o4_obs_len. lia.
Qed.
Lemma o4_ew_x : forall cx E regs xs k d, (563 <= k)%nat -> (k - 563 < length xs)%nat ->
  ew (d_env cx E (obs_vals regs ++ xs)) k = nth (k - 563) xs d.
Proof.
intros cx E regs xs k d Hk Hj. unfold d_env. replace k with (530 + (33 + (k - 563)))%nat at 1 by lia.
rewrite (ew_havoc_new E 530 _ (33 + (k - 563)) d) by (cbn [length]; rewrite length_app, o4_obs_len; lia).
replace (33 + (k - 563))%nat with (S (32 + (k - 563))) by lia. cbn [nth].
rewrite app_nth2 by (rewrite o4_obs_len; lia). rewrite o4_obs_len. f_equal. lia.
Qed.
Lemma o4_regs_ok : forall B cx E regs xs, d_E cx E -> d_rL B cx regs -> 0 <= d_A cx < 2 ^ 64 ->
  regs_ok (d_env cx E (obs_vals regs ++ xs)) obs_sr regs.
Proof.
intros B cx E regs xs HE HL HA.
pose proof (regs_ok_obs B cx E regs HE HL HA) as R.
apply regs_ok_by_cases. intros r Hr. rewrite (R r).
cbv [all_regs In] in Hr.
repeat match goal with Hx : _ \/ _ |- _ => destruct Hx as [<-|Hx] end; [ .. | contradiction ];
  (match goal with |- sv_denot _ (sr_get ?sr ?r) = _ =>
     let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end);
  first [ reflexivity | cbn [sv_denot]; rewrite o4_ew_app by lia; reflexivity ].
Qed.
Lemma o4_kept_mbyte : forall H (m m2 : word -> option byte) a,
  aview SEGS H m2 a = aview SEGS H m a -> mbyte SEGS (mrestrict H m2) a = mbyte SEGS (mrestrict H m) a.
Proof. intros H m m2 a E. exact (mbyte_of_aview SEGS H H m m2 a E). Qed.
Lemma o4_vm_keep : forall (W : world SEGS) (m m2 : word -> option byte) a n v,
  (forall j, 0 <= j < Z.of_nat n -> aview SEGS (w_H W) m2 (a + j) = aview SEGS (w_H W) m (a + j)) ->
  val_mem SEGS (rd W m) a n v -> val_mem SEGS (rd W m2) a n v.
Proof. intros W m m2 a n v Hk H j Hj. rewrite (o4_kept_mbyte _ m m2 _ (Hk (Z.of_nat j) ltac:(lia))). exact (H j Hj). Qed.
Lemma o4_garr8_keep : forall (W : world SEGS) (m m2 : word -> option byte) a l,
  (forall j, 0 <= j < Z.of_nat (length l) -> aview SEGS (w_H W) m2 (a + j) = aview SEGS (w_H W) m (a + j)) ->
  garr8 SEGS (rd W m) a l -> garr8 SEGS (rd W m2) a l.
Proof.
intros W m m2 a l Hk H j Hj. destruct (H j Hj) as [H1 H2]. split; [|exact H2].
apply (o4_vm_keep W m m2 _ 1 _); [|exact H1].
intros k Hk'. replace (a + Z.of_nat j + k) with (a + Z.of_nat j) by lia. apply Hk. lia.
Qed.
Lemma o4_rok_keep : forall E H (m m2 : word -> option byte) n b lo hi wlo whi cs,
  bv_unsigned (ew E n) = b ->
  (forall a, b + lo <= a < b + hi -> aview SEGS H m2 a = aview SEGS H m a) ->
  (forall a, apresent H m a -> apresent H m2 a) ->
  forallb (fun c => match YP09.c_val c with CData _ _ _ => false | _ => true end) cs = true ->
  forallb (chunk_inside (YP09.mkRegion (Some n) lo hi wlo whi cs)) cs = true ->
  region_ok SEGS E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  region_ok SEGS E (mrestrict H m2) (YP09.mkRegion (Some n) lo hi wlo whi cs).
Proof.
intros E H m m2 n b lo hi wlo whi cs Hn Hav Hp Hnc Hci HR.
destruct (region_kept_aview E H m m2 n b lo hi wlo whi cs Hn Hav Hp) as [K1 K2].
apply (YI04.region_ok_transport SEGS E E _ _ _ HR eq_refl); [| exact K1 | exact K2 | exact Hci].
intros c Hc. pose proof (proj1 (forallb_forall _ _) Hnc c Hc) as Hx. cbv beta in Hx.
destruct (YP09.c_val c); [reflexivity | exact I | exact I | discriminate Hx].
Qed.
Lemma o4_rdword_keep : forall (rd rd' : reader) a, (forall j, 0 <= j < 8 -> rd' (a + j) = rd (a + j)) -> rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. pose proof (H 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. unfold rdword.
rewrite H0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.
Lemma o4_aview_present : forall H (m : word -> option byte) a, apresent H m a -> aview SEGS H m a <> None.
Proof. intros H m a [Hh [b Hb]]. unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate. Qed.
Lemma o4_dsh_zero : forall lo (len : nat), forallb (fun j => dsh_rec (lo + Z.of_nat j) =? 0) (seq 0 len) = true ->
  forall k, lo <= k < lo + Z.of_nat len -> dsh_rec k = 0.
Proof.
intros lo len H k Hk. pose proof (proj1 (forallb_forall _ _) H (Z.to_nat (k - lo)) ltac:(apply in_seq; lia)) as Hx.
cbv beta in Hx. rewrite Z2Nat.id in Hx by lia. replace (lo + (k - lo)) with k in Hx by lia. apply Z.eqb_eq. exact Hx.
Qed.
Lemma o4_frame_keep : forall cx h (W : world SEGS) (m m2 : word -> option byte) lo hi,
  d_frame cx h dsh_rec W m -> d_shadow cx dsh_rec W m ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) m a) ->
  (forall a, apresent (w_H W) m a -> apresent (w_H W) m2 a) ->
  4096 <= d_FB cx -> d_FB cx + 4096 <= alloc_ceiling -> alloc_ceiling + LLVMF_STK <= d_S cx <= 2 ^ 47 ->
  d_S cx - 592 <= d_A cx <= d_S cx - 576 -> alloc_ceiling <= lo -> hi <= d_A cx ->
  d_frame cx h dsh_rec W m2 /\ d_shadow cx dsh_rec W m2.
Proof.
intros cx h W m m2 lo hi (E & HE & HR & Hfl & H216 & H152) Hsh KP PR HF0 HF1 HS HA Hlo Hhi.
pose proof alloc_ceiling_val as AC. unfold LLVMF_STK in HS.
pose proof HE as (EE & E32 & HEI & E60 & EF & ESH).
assert (US : bv_unsigned (ew E 2) = d_S cx) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (UA : bv_unsigned (ew E 60) = d_A cx)
  by (change 60%nat with AT_A; rewrite E60; unfold w64; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
assert (UF : bv_unsigned (ew E 516) = d_FB cx)
  by (change 516%nat with AT_F; rewrite EF; unfold w64; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
assert (USH : bv_unsigned (ew E 529) = shadow_addr (d_FB cx))
  by (change 529%nat with AT_SH; rewrite ESH; unfold w64; rewrite Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus;
      unfold shadow_addr, SHADOW_OFF; lia).
split.
- exists E. split; [exact HE|]. split; [|split; [|split]].
  + unfold d_regions in HR |- *. rewrite fs6 in *. unfold fshadow_region in *. rewrite fs6 in *.
    apply Forall_cons_iff in HR as [R1 HR]. apply Forall_cons_iff in HR as [R2 HR].
    apply Forall_cons_iff in HR as [R3 HR]. apply Forall_cons_iff in HR as [R4 _].
    repeat apply Forall_cons; try apply Forall_nil.
    * apply (o4_rok_keep E (w_H W) m m2 AT_STK (d_S cx) _ _ _ _ _ US); [ | exact PR | vm_compute; reflexivity | vm_compute; reflexivity | exact R1].
      intros a Ha. apply KP; lia.
    * apply (o4_rok_keep E (w_H W) m m2 AT_A (d_A cx) _ _ _ _ _ UA); [ | exact PR | vm_compute; reflexivity | vm_compute; reflexivity | exact R2].
      intros a Ha. apply KP; lia.
    * apply (o4_rok_keep E (w_H W) m m2 AT_F (d_FB cx) _ _ _ _ _ UF); [ | exact PR | vm_compute; reflexivity | vm_compute; reflexivity | exact R3].
      intros a Ha. apply KP; lia.
    * apply (o4_rok_keep E (w_H W) m m2 AT_SH (shadow_addr (d_FB cx)) _ _ _ _ _ USH); [ | exact PR | vm_compute; reflexivity | vm_compute; reflexivity | exact R4].
      intros a Ha. apply KP; unfold shadow_addr, SHADOW_OFF in *; lia.
  + rewrite (o4_rdword_keep (aview SEGS (w_H W) m)); [exact Hfl|]. intros j Hj. apply KP; rewrite fs6; lia.
  + apply (o4_vm_keep W m m2 _ 8 h); [|exact H216]. intros j Hj. apply KP; lia.
  + apply (o4_vm_keep W m m2 _ 8 (h + 440)); [|exact H152]. intros j Hj. apply KP; lia.
- intros k Hk. rewrite KP; [exact (Hsh k Hk) | | ]; unfold shadow_addr, SHADOW_OFF, DFRAME_SH in *; lia.
Qed.

Section h.
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable tfib_K : asink_syms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ABCMP : forall fq : YK11.FPState, abcmp_realizes (fx := fq) SEGS B (SIGMA DS___interceptor_trampoline_bcmp).
#[local] Notation DAT := (d_at B MT XM_LIB RLO RHI tfib_K).
#[local] Notation oc := (oc B).
#[local] Notation ob_c10 := (ob_c10 B MT XM_LIB RLO RHI tfib_K).
#[local] Notation r27 := (r27_in B MT XM_LIB RLO RHI tfib_K).

Lemma o4_body_n : forall cx h n n' xb shf ly S W m, d_body B cx h n xb shf ly S W m ->
  0 <= n' <= Z.max 0 (c_n cx - 7) -> d_body B cx h n' xb shf ly S W m.
Proof.
intros cx h n n' xb shf ly S W m (T & G & Lk & H & Hf & Hs & Ho & Hb & (_ & Hg & Hoi) & Hi & Hoff & Hgeo & Hcn & Hstk & Haw) Hn.
exists T, G, Lk, H. exact (conj Hf (conj Hs (conj Ho (conj Hb (conj (conj Hn (conj Hg Hoi)) (conj Hi (conj Hoff (conj Hgeo (conj Hcn (conj Hstk Haw)))))))))).
Qed.

Lemma o4_land : forall (fq : YK11.FPState) cx h i now nb fr len n ly3 S3 (W : world SEGS) mem0 md k acc E vals ss ms,
  lib.Lib.FP.frm0 (@YK11.fp_csr fq) ->
  d_base B MT XM_LIB RLO RHI tfib_K cx ->
  ajournal SEGS B LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
    [(DFRAME_CLASS, c_fpos cx)] ly3 S3 W (ms_mem ms) md k ->
  frames S3 = [(DFRAME_CLASS, c_fpos cx)] -> 0 <= k <= EV_HEAD i + 1 -> st_nev S3 <= st_nev (c_S cx) + (EV_HEAD i + 1) ->
  mo_le MT (c_S cx) S3 acc -> acc <= ACC_HEAD MT i + mo_malloc MT REC_MAX ->
  d_E cx E -> st_ok_pi (fx := fq) SEGS VAL (d_env cx E vals) ss (restrict (w_H W) ms) ->
  ss_pc ss = R27_OFF -> ss_resv ss = None -> d_land_chk dsh_rec (ss_mem ss) = true ->
  (forall x, ms_mem ms x = mem0 x) ->
  0 <= i < MAX_OPS -> 0 <= now < 2 ^ 64 -> len <= nb -> nb - len <= Z.max 0 (c_n cx - 7) ->
  d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W mem0 -> d_sp0 cx i now W mem0 -> d_frm cx nb fr len W mem0 ->
  d_rL B cx (ms_regs ms) -> getr (ms_regs ms) 14 = w64 (d_cur cx nb) -> getr (ms_regs ms) 24 = w64 len ->
  getr (ms_regs ms) 23 = w64 nb -> getr (ms_regs ms) 27 = w64 fr -> getr (ms_regs ms) 22 = w64 (d_obj cx OS) ->
  getr (ms_regs ms) 26 = w64 (d_obj cx OOUR) ->
  r27 cx h i (nb - len) now nb fr len W (mkCfg ms md).
Proof.
intros fq cx h i now nb fr len n ly3 S3 W mem0 md k acc E vals ss ms Hf0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HdE HS Hpc Hrv Hchk MP
  Hi Hnow Hlen Hnb Hbody Hsp0 Hfrm HrL R14 R24 R23 R27 R22 R26.
assert (MPr : forall x, rd W (ms_mem ms) x = rd W mem0 x) by (intros x; unfold mrestrict; rewrite MP; reflexivity).
pose proof (st_ok_pi_restrict_mkst (w_H W) _ ss ms HS Hrv) as Hms. rewrite Hpc in Hms.
destruct (ob_A_range B cx ly3 S3 W (ms_mem ms) md k HJ) as (HSr & HS16 & HAr & HA32).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _ & _ & _ & (Hn & _) & _).
pose proof Hframe as (E0 & _ & _ & _ & Hh216 & Hh152).
assert (Hctx : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W (ms_mem ms) md k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_land B MT XM_LIB RLO RHI tfib_K LAWS FFL fq cx h dsh_rec ly3 S3 W md k (d_env cx E vals) ss ms Hctx
  (d_E_env cx E vals HdE) (d_env_fl cx E vals) HS Hchk (val_mem_pt _ _ _ _ _ MPr Hh216) (val_mem_pt _ _ _ _ _ MPr Hh152))
  as [Hframe4 Hshadow4].
assert (Hbody4 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W (ms_mem ms)).
{ apply (d_body_rt B cx h n n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem0 (ms_mem ms) (d_A cx) (d_A cx) (fun _ => False) Hbody).
  - unfold LLVMF_STK; lia.
  - lia.
  - intros a [].
  - intros a Ha _. unfold aview, mbyte. rewrite MPr. reflexivity.
  - intros a _ [Hh [b Hb]]. split; [exact Hh|]. exists b. rewrite MP. exact Hb.
  - exact Hframe4.
  - exact Hshadow4.
  - lia. }
pose proof (o4_body_n cx h n (nb - len) _ _ _ _ _ _ Hbody4 ltac:(lia)) as Hbody5.
unfold r27_in, d_arm_at_pf, d_at.
exists fq, ly3, S3, (ms_regs ms), (ms_mem ms), md, k, acc.
split; [unfold cfg_at, w64; rewrite <- Hms; reflexivity|].
split; [exact Hf0|]. split; [exact Hbase|]. split; [exact HJ|]. split; [exact Hfrs|]. split; [exact Hk|].
split; [exact Hnev|]. split; [exact Hmo|]. split; [exact Hacc|].
split; [exact Hi|]. split; [lia|]. split; [exact Hnow|]. split; [exact HrL|].
split; [repeat split; assumption|].
split; [destruct Hfrm as (F1 & F2 & Fn & F3); split; [split; [exact F1|]; split; [exact F2|]; split; [exact Fn|]; exact (garr8_pt _ _ _ _ MPr F3)|];
  split; [exact Hlen | reflexivity]|].
split; [destruct Hsp0 as (S1 & S2); split; eapply val_mem_pt; [exact MPr | exact S1 | exact MPr | exact S2]|].
exact Hbody5.
Qed.

Definition o4_ret (cx : dcx) (h i n now op nb fr len : Z) (Sg : list byte) (kmax accmax : Z) : world SEGS -> config -> Prop :=
  DAT cx 0x1bc0 kmax accmax (fun regs ly3 S3 W3 mem3 md3 => exists T T' ow,
    oc cx h i n now op nb fr len Sg T' regs ly3 S3 W3 mem3 /\ getr regs 26 = w64 (d_obj cx OOUR) /\
    length T = 400%nat /\ 0 <= n_of T < 8 /\ (T', 1) = reac_disco_table_observe_c.observe_new T Sg ow now /\
    (ow = 0 \/ ow = 1) /\ val_mem SEGS (rd W3 mem3) (d_A cx + 408) 8 ow /\
    getr regs 21 = w64 (d_obj cx OT + 48 * n_of T) /\ getr regs 22 = w64 (d_obj cx OS) /\ getr regs 10 = w64 0 /\
    getr regs 23 = w64 nb /\ getr regs 24 = w64 len /\ getr regs 27 = w64 fr).

Lemma o4_h1 : forall cx h i n now op nb fr len Sg W c,
  ob_c10 cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c ->
  SRr SEGS W c (fun W' c' => r27 cx h i (nb - len) now nb fr len W' c' \/
    o4_ret cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W' c').
Proof.
intros cx h i n now op nb fr len Sg W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ai & ow & ret & HOC & H26 & HobT & HrT & HrX & Hai & H13 & H14).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & Hshadow & _ & Hblocks & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
destruct HobT as (HTl0 & HTok0 & HFR & How & Hsp22 & H408 & HOM).
destruct HrT as (H19 & H22a). destruct HrX as (H21 & H23 & H24 & H27).
pose proof HTok0 as (HT1 & _). unfold tbl_T1 in HT1.
pose proof (slot_observe.unknown_arm T Sg ow now T' ret ai HFR Hai HOM) as ARM.
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
destruct (d_geom B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k HctxD)
  as (_ & _ & _ & HF0 & HF1 & HFapp & _ & HF32 & HFpres & HSpres & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
pose proof (o4_u_range T' 384 4 ltac:(lia) ltac:(rewrite HTl; cbn; lia)) as Hu1.
pose proof (o4_u_range T' 388 4 ltac:(lia) ltac:(rewrite HTl; cbn; lia)) as Hu2.
change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32) in Hu1, Hu2.
set (xs1 := [w64 (u_at T' 384 4); w64 (u_at T' 388 4)]).
assert (FC : Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ xs1)) (rd W mem3) (d_FB cx))
  [YP09.mkChunk 2544 (CVal 4 (SOff 563 0)); YP09.mkChunk 2548 (CVal 4 (SOff 564 0))]).
{ apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 4 _ (u_at T' 384 4)); [ | exact Hu1 | lia | ].
    + apply o4_sv_atom. rewrite (o4_ew_x cx E regs xs1 563 (Z_to_bv 64 0)) by (unfold xs1; cbn; lia). reflexivity.
    + replace (d_FB cx + 2544) with (d_obj cx OT + 384) by (unfold d_obj, dobj_off; lia).
      exact (o4_val_mem_sub _ _ T' 384 4 HT ltac:(lia) ltac:(rewrite HTl; cbn; lia)).
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 4 _ (u_at T' 388 4)); [ | exact Hu2 | lia | ].
    + apply o4_sv_atom. rewrite (o4_ew_x cx E regs xs1 564 (Z_to_bv 64 0)) by (unfold xs1; cbn; lia). reflexivity.
    + replace (d_FB cx + 2548) with (d_obj cx OT + 388) by (unfold d_obj, dobj_off; lia).
      exact (o4_val_mem_sub _ _ T' 388 4 HT ltac:(lia) ltac:(rewrite HTl; cbn; lia)). }
pose proof (o4_regs_ok B cx E regs xs1 HdE HrL HAr2) as RO1.
pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0x1b78 obs_sr
  (obs_vals regs ++ xs1) [] [YP09.mkChunk 2544 (CVal 4 (SOff 563 0)); YP09.mkChunk 2548 (CVal 4 (SOff 564 0))] []
  (d_facts [] []) HctxD HdE Hregs Hflag RO1
  (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E _ [] [] HctxD HdE I I)
  (Forall_nil _) FC (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS.
unfold ss_d in HS.
ro_base HS 516%nat. ro_base HS 529%nat. ro_base HS 60%nat.
assert (EW516 : ew (d_env cx E (obs_vals regs ++ xs1)) 516 = Z_to_bv 64 (d_FB cx)).
{ rewrite d_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & _ & EF & _). exact EF. }
assert (EW60 : ew (d_env cx E (obs_vals regs ++ xs1)) 60 = Z_to_bv 64 (d_A cx)).
{ rewrite d_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & EA & _). exact EA. }
assert (SV550 : sv_denot (d_env cx E (obs_vals regs ++ xs1)) (SOff 550 0) = Z_to_bv 64 (n_of T)).
{ pose proof (RO1 19%bv) as R. o4_rr R. rewrite H19 in R. symmetry. exact R. }
pose proof (o4_ew_of_sv _ _ _ SV550) as EW550.
assert (SV552 : sv_denot (d_env cx E (obs_vals regs ++ xs1)) (SOff 552 0) = Z_to_bv 64 ret).
{ pose proof (RO1 21%bv) as R. o4_rr R. rewrite H21 in R. symmetry. exact R. }
assert (EW563 : ew (d_env cx E (obs_vals regs ++ xs1)) 563 = Z_to_bv 64 (u_at T' 384 4))
  by (rewrite (o4_ew_x cx E regs xs1 563 (Z_to_bv 64 0)) by (unfold xs1; cbn; lia); reflexivity).
assert (EW564 : ew (d_env cx E (obs_vals regs ++ xs1)) 564 = Z_to_bv 64 (u_at T' 388 4))
  by (rewrite (o4_ew_x cx E regs xs1 564 (Z_to_bv 64 0)) by (unfold xs1; cbn; lia); reflexivity).
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs ++ xs1))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs ++ xs1)) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (MP : forall x, mem3 x = mem3 x) by reflexivity.
unfold cfg_at. change (w64 (BASE + 0x1b78)) with (Z_to_bv 64 (BASE + 0x1b78)).
o4_run RUN.
psrr_branch_tok RUN BR HS SHOK OBspan.
- rewrite (o4_br_lt7 _ (n_of T) EW550 ltac:(lia)) in Hc. apply Z.ltb_lt in Hc. rename Hc into HN7.
  destruct ARM as [(HN8 & EF) | (HN8 & _)]; [|lia].
  destruct (slot_observe.full_facts T T' ret HTl0 EF) as (_ & Hret0 & E384 & E388 & _ & _).
  assert (Hn8 : bv_swrap 32 (u_at T' 384 4) = n_of T) by exact (slot_observe.n_of_sub T T' E384).
  assert (Hov : bv_swrap 32 (u_at T' 388 4) <> 0).
  { change (bv_swrap 32 (u_at T' 388 4)) with (ov_of T'). unfold ov_of, s32_at, u_at. rewrite E388.
    destruct (Z.eqb_spec (ov_of T) 0) as [_|Hz]; [intros Hx; vm_compute in Hx; discriminate Hx | exact Hz]. }
  o4_run RUN.
  psrr_branch_tok RUN BR HS SHOK OBspan.
  + exfalso. rewrite (o4_br_ne_false _ (SOff 552 0) (SLit 0)) in Hc; [discriminate Hc|]. rewrite SV552, Hret0. reflexivity.
  + clear Hc. o4_run RUN.
    psrr_branch_tok RUN BR HS SHOK OBspan.
    * exfalso. rewrite (o4_br_ne_false _ (SExt true 32 (SOff 563 0)) (SOff 550 0)) in Hc; [discriminate Hc|].
      rewrite (o4_sv_sext32 _ 563 _ EW563 Hu1), SV550, Hn8. reflexivity.
    * clear Hc. o4_run RUN.
      psrr_branch_tok RUN BR HS SHOK OBspan.
      -- exfalso. rewrite (o4_br_eq_false _ (SExt true 32 (SOff 564 0)) (SLit 0) (bv_swrap 32 (u_at T' 388 4)) 0) in Hc;
           [discriminate Hc | exact (o4_sv_sext32 _ 564 _ EW564 Hu2) | reflexivity | apply o4_mod_nz; [exact Hov | apply swrap32_range]].
      -- clear Hc. o4_runto RUNTO 6984.
         repeat rewrite wvb_collapse in HJ.
         apply SRr_ret. left.
         lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?ms) |- _ =>
           assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 14; 18; 20; 23; 24; 25; 26; 27]%bv ->
             getr (ms_regs ms) r = getr regs r)
             by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS), (RO1 r); cbv [In] in Hr;
                 repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
           assert (R22 : getr (ms_regs ms) 22%bv = w64 (d_obj cx OS))
             by (rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms 22%bv HS);
                 match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
                 cbn [sv_denot]; rewrite EW516, w64_add_w; reflexivity);
           apply (o4_land fq cx h i now nb fr len n ly3 S3 W mem3 _ k acc E _ ss ms Hf0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HdE HS
             ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) MP
             Hi Hnow Hlen Hnb Hbody Hsp0 Hfrm)
         end.
         ++ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25). unfold d_rL, spZ in *.
            rewrite (RG 2%bv), (RG 3%bv), (RG 4%bv), (RG 8%bv), (RG 9%bv), (RG 18%bv), (RG 20%bv), (RG 25%bv) by (cbv; tauto).
            repeat split; assumption.
         ++ rewrite (RG 14%bv) by (cbv; tauto). exact H14.
         ++ rewrite (RG 24%bv) by (cbv; tauto). exact H24.
         ++ rewrite (RG 23%bv) by (cbv; tauto). exact H23.
         ++ rewrite (RG 27%bv) by (cbv; tauto). exact H27.
         ++ exact R22.
         ++ rewrite (RG 26%bv) by (cbv; tauto). exact H26.
- rewrite (o4_br_lt7 _ (n_of T) EW550 ltac:(lia)) in Hc. apply Z.ltb_ge in Hc. rename Hc into HN7.
  destruct ARM as [(HN8 & _) | (HN8 & EN)]; [lia|].
  destruct (slot_observe.new_facts T Sg ow now T' ret HTl0 HSgl ltac:(lia) EN) as (_ & Hret1 & E384 & _ & NF).
  subst ret.
  assert (Hu1v : u_at T' 384 4 = n_of T + 1).
  { unfold u_at. rewrite E384. apply o4_u_le. change (2 ^ (8 * Z.of_nat 4)) with (2 ^ 32). lia. }
  o4_run RUN.
  psrr_branch_tok RUN BR HS SHOK OBspan.
  + exfalso. rewrite (o4_br_ne_false _ (SOff 552 0) (SLit 1)) in Hc; [discriminate Hc|]. rewrite SV552. reflexivity.
  + clear Hc. o4_run RUN.
    psrr_branch_tok RUN BR HS SHOK OBspan.
    * exfalso. rewrite (o4_br_ne_false _ (SExt true 32 (SOff 563 0)) (SAluw ALU_ADD (SOff 550 0) (SLit 1))) in Hc; [discriminate Hc|].
      rewrite (o4_sv_sext32 _ 563 _ EW563 Hu1), (o4_sv_aluw1 _ (n_of T) EW550 ltac:(lia)), Hu1v.
      rewrite swrap32_id by lia. reflexivity.
    * clear Hc. o4_run RUN.
      repeat rewrite wvb_collapse in HJ.
      lazymatch goal with HS : st_ok _ _ _ (restrict _ ?m) |- _ => rename m into msc end.
      lazymatch goal with HS : st_ok _ ?Ex ?ssx (restrict _ msc) |- _ =>
        pose proof (st_ok_restrict_mkst SEGS (w_H W) Ex ssx msc HS eq_refl) as Hms;
        pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 10%bv HS) as Ra0;
        pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 11%bv HS) as Ra1;
        pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 12%bv HS) as Ra2;
        pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 1%bv HS) as Rra;
        pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 2%bv HS) as Rsp;
        pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 21%bv HS) as R21;
        pose proof (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc 22%bv HS) as R22;
        assert (RG : forall r : bv 5, In r [3; 4; 8; 9; 18; 20; 23; 24; 25; 26; 27]%bv -> getr (ms_regs msc) r = getr regs r)
          by (intros r Hr; rewrite (st_ok_restrict_reg SEGS (w_H W) Ex ssx msc r HS), (RO1 r); cbv [In] in Hr;
              repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr)
      end.
      assert (MPv : forall a, aview SEGS (w_H W) (ms_mem msc) a = aview SEGS (w_H W) mem3 a)
        by (intros a; unfold aview, mbyte, mrestrict; rewrite MP; reflexivity).
      cbn [ss_pc setpc] in Hms.
      o4_rr Ra0. o4_rr Ra1. o4_rr Ra2. o4_rr Rra. o4_rr Rsp. o4_rr R21. o4_rr R22.
      rewrite (o4_sv_addr _ (d_FB cx) 2160 (n_of T) EW516 EW550) in Ra0, R21.
      cbn [sv_denot] in Ra1, Ra2, R22. rewrite EW516, w64_add_w in Ra1, R22.
      change (SOff 240 7104) with (SOff A_TEXT 7104) in Rra. rewrite (codeptr_val _ 7104 HEI) in Rra.
      rewrite (o4_sv_atom _ 60 (d_A cx) EW60) in Rsp.
      assert (SPZ : spZ (ms_regs msc) = d_A cx)
        by (unfold spZ; rewrite Rsp, Z_to_bv_unsigned; apply bv_wrap_small; unfold bv_modulus; lia).
      pose proof alloc_ceiling_val as ACV.
      rewrite Hms.
      eapply SRr_bind.
      { eapply (aj_bcmp_at (fx := fq) SEGS B LAWS pa_segs_low (SIGMA DS___interceptor_trampoline_bcmp) (ABCMP fq) W
          (ms_regs msc) (ms_mem msc) LLVMF_STK (d_S cx) [] (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx)
          [(DFRAME_CLASS, c_fpos cx)] ly3 S3 _ k (d_obj cx OT + 48 * n_of T) (d_obj cx OS) 6 (d_A cx - d_S cx)
          (Z_to_bv 64 (BASE + 7104)) HJ).
        - rewrite Ra0. unfold w64, d_obj, dobj_off. f_equal; lia.
        - rewrite Ra1. unfold w64, d_obj, dobj_off. reflexivity.
        - rewrite Ra2. reflexivity.
        - lia.
        - unfold d_obj, dobj_off; lia.
        - unfold d_obj, dobj_off; lia.
        - unfold d_obj, dobj_off; lia.
        - unfold d_obj, dobj_off; lia.
        - rewrite SPZ. lia.
        - lia.
        - lia.
        - unfold ESTACK, LLVMF_STK; lia.
        - destruct HrL as (_ & Hgp & _). rewrite (RG 3%bv) by (cbv; tauto). exact Hgp.
        - destruct HrL as (_ & _ & Htp & _). rewrite (RG 4%bv) by (cbv; tauto). exact Htp.
        - exact Rra.
        - apply ret_ok_codeptr_v; [lia | reflexivity].
        - intros a Ha. rewrite MPv, SPZ. unfold d_obj, dobj_off in Ha. split.
          + apply o4_aview_present. apply HFpres. lia.
          + unfold ESTACK, LLVMF_STK in *. lia.
        - intros a Ha. rewrite MPv, SPZ. unfold d_obj, dobj_off in Ha. split.
          + apply o4_aview_present. apply HFpres. lia.
          + unfold ESTACK, LLVMF_STK in *. lia.
        - intros a Ha. unfold ESTACK, LLVMF_STK, d_obj, dobj_off in *. lia.
        - intros a Ha. unfold ESTACK, LLVMF_STK, d_obj, dobj_off in *. lia.
        - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, d_obj, dobj_off.
          unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia.
        - unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd, d_obj, dobj_off.
          unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in HFapp. lia.
        - intros a Ha. exists 0. split; [|left; reflexivity]. rewrite MPv. unfold shadow_of_addr.
          unfold d_obj, dobj_off in Ha.
          replace (SHADOW_OFF + a / 8) with (shadow_addr (d_FB cx) + (a / 8 - d_FB cx / 8)) by (unfold shadow_addr; lia).
          rewrite Hshadow by (unfold DFRAME_SH; lia).
          f_equal. apply (o4_dsh_zero 270 50); [vm_compute; reflexivity | lia].
        - intros _ s Hs. rewrite MPv. apply o4_aview_present.
          replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
          apply HSpres. unfold shadow_addr, SHADOW_OFF, d_obj, dobj_off in *. lia.
        - intros a Ha. exists 0. split; [|left; reflexivity]. rewrite MPv. unfold shadow_of_addr.
          unfold d_obj, dobj_off in Ha.
          replace (SHADOW_OFF + a / 8) with (shadow_addr (d_FB cx) + (a / 8 - d_FB cx / 8)) by (unfold shadow_addr; lia).
          rewrite Hshadow by (unfold DFRAME_SH; lia).
          f_equal. apply (o4_dsh_zero 374 3); [vm_compute; reflexivity | lia].
        - intros _ s Hs. rewrite MPv. apply o4_aview_present.
          replace s with (shadow_addr (d_FB cx) + (s - shadow_addr (d_FB cx))) by lia.
          apply HSpres. unfold shadow_addr, SHADOW_OFF, d_obj, dobj_off in *. lia. }
      cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & HJ2 & HP & Hv & Hcmp & Hfr & Hpres).
      assert (KP : forall a, 0 <= a < 2 ^ 64 -> ~ (d_A cx - 8192 <= a < d_A cx) ->
        aview SEGS (w_H W) mem2 a = aview SEGS (w_H W) mem3 a).
      { intros a Ha Hna. rewrite (Hfr a Ha) by (unfold ESTACK; lia). apply MPv. }
      assert (PR : forall a, apresent (w_H W) mem3 a -> apresent (w_H W) mem2 a).
      { intros a [Hh [b Hb]]. apply Hpres. split; [exact Hh|]. exists b. rewrite MP. exact Hb. }
      assert (EM : sub T' (48 * n_of T) 6 = sub Sg 0 6).
      { replace (48 * n_of T) with (48 * n_of T + 0) by lia. rewrite (NF 0 6%nat) by (cbn; lia).
        destruct (slot_observe.new_fields Sg ow now HSgl) as (F0 & _). exact F0. }
      assert (Hv0 : v = w64 0).
      { apply (proj2 Hcmp). intros j Hj. rewrite !MPv.
        replace (d_obj cx OT + 48 * n_of T + j) with (d_obj cx OT + Z.of_nat (Z.to_nat (48 * n_of T + j))) by lia.
        replace (d_obj cx OS + j) with (d_obj cx OS + Z.of_nat (Z.to_nat j)) by lia.
        rewrite (o4_aview_garr8 _ _ _ T' _ HT) by (rewrite HTl; lia).
        rewrite (o4_aview_garr8 _ _ _ Sg _ HSg) by (rewrite HSgl; lia).
        f_equal. f_equal.
        transitivity (nth (Z.to_nat j) (sub T' (48 * n_of T) 6) (Z_to_bv 8 0)).
        - rewrite o4_nth_sub by lia. f_equal. lia.
        - rewrite EM, o4_nth_sub by lia. reflexivity. }
      destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25).
      pose proof (o4_frame_keep cx h W mem3 mem2 (d_A cx - 8192) (d_A cx) Hframe Hshadow KP PR HF0 HF1 HSr HAr
        ltac:(unfold LLVMF_STK in HSr; lia) ltac:(lia)) as [HF2 HSh2].
      assert (Hbody2 : d_body B cx h n (dxb fr len) dsh_rec ly3 S3 W mem2).
      { apply (d_body_call_keep B MT XM_LIB RLO RHI tfib_K LAWS cx h n (dxb fr len) dsh_rec dsh_rec ly3 S3 W mem3 ly3 S3 W mem2 md2 k
          (d_A cx - 8192) (d_A cx) Hbody (conj Hbase HJ2)); [unfold LLVMF_STK in *; lia | lia | exact KP | apply Permutation_refl | exact HF2 | exact HSh2]. }
      apply SRr_ret. right. unfold o4_ret, d_at.
      exists fq, ly3, S3, regs2, mem2, md2, k, acc.
      split; [unfold cfg_at, w64; reflexivity|].
      split; [exact Hf0|]. split; [exact Hbase|]. split; [exact HJ2|]. split; [exact Hfrs|]. split; [exact Hk|]. split; [exact Hnev|].
      split; [exact Hmo|]. split; [exact Hacc|].
      exists T, T', ow.
      split.
      { unfold DiscoEntObsCuts.oc.
        refine (conj Hi (conj Hn (conj Hnow (conj Hop (conj Hop2 (conj _ (conj _ (conj _ (conj HSgl (conj _ (conj HSf
          (conj _ (conj _ (conj _ (conj _ (conj Hlen (conj Hnb (conj HTl (conj _ (conj HTok Hbody2)))))))))))))))))))).
        - unfold d_rL, spZ.
          rewrite (o4_pres _ _ 2%bv HP), (o4_pres _ _ 3%bv HP), (o4_pres _ _ 4%bv HP), (o4_pres _ _ 8%bv HP),
            (o4_pres _ _ 9%bv HP), (o4_pres _ _ 18%bv HP), (o4_pres _ _ 20%bv HP), (o4_pres _ _ 25%bv HP)
            by o4_cs.
          rewrite (RG 3%bv), (RG 4%bv), (RG 8%bv), (RG 9%bv), (RG 18%bv), (RG 20%bv), (RG 25%bv) by (cbv; tauto).
          split; [exact SPZ|]. repeat split; assumption.
        - destruct Hsp0 as (S1 & S2). split.
          + apply (o4_vm_keep W mem3 mem2 _ 8 _); [intros j Hj; apply KP; lia | exact S1].
          + apply (o4_vm_keep W mem3 mem2 _ 8 _); [intros j Hj; apply KP; lia | exact S2].
        - destruct Hfrm as (F1 & F2 & Fn & F3). split; [exact F1|]. split; [exact F2|]. split; [exact Fn|].
          apply (o4_garr8_keep W mem3 mem2); [|exact F3]. intros j Hj. rewrite length_map, length_firstn in Hj.
          destruct (Z.eq_dec fr 0) as [Hz|Hz]; [rewrite (F2 Hz) in Hj; cbn in Hj; lia|].
          pose proof Hblocks as (Hperm & _).
          assert (Hin : In (fr, len) (ablocks B ly3 S3)).
          { apply (Permutation_in _ (Permutation_sym Hperm)). unfold dxb.
            replace (fr =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hz). left; reflexivity. }
          pose proof HJ as (HAR3 & _).
          destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 Hin) as (_ & Hp4k & Hpc & _).
          assert (Hrq : len <= req_size len) by (unfold req_size; destruct (Z.eqb_spec len 0); lia).
          apply KP; unfold LLVMF_STK in *; lia.
        - apply (o4_garr8_keep W mem3 mem2); [|exact HSg]. intros j Hj. rewrite length_map, HSgl in Hj.
          apply KP; unfold d_obj, dobj_off, LLVMF_STK in *; lia.
        - apply (o4_vm_keep W mem3 mem2 _ 8 _); [intros j Hj; apply KP; lia | exact H248].
        - apply (o4_vm_keep W mem3 mem2 _ 8 _); [intros j Hj; apply KP; lia | exact H336].
        - apply (o4_vm_keep W mem3 mem2 _ 8 _); [intros j Hj; apply KP; lia | exact H368].
        - apply (o4_vm_keep W mem3 mem2 _ 8 _); [intros j Hj; apply KP; lia | exact H280].
        - apply (o4_garr8_keep W mem3 mem2); [|exact HT]. intros j Hj. rewrite length_map, HTl in Hj.
          apply KP; unfold d_obj, dobj_off, LLVMF_STK in *; lia. }
      split; [rewrite (o4_pres _ _ 26%bv HP) by o4_cs; rewrite (RG 26%bv) by (cbv; tauto); exact H26|].
      split; [exact HTl0|]. split; [lia|]. split; [exact EN|]. split; [exact How|].
      split; [apply (o4_vm_keep W mem3 mem2 _ 8 _); [intros j Hj; apply KP; lia | exact H408]|].
      split; [rewrite (o4_pres _ _ 21%bv HP) by o4_cs; rewrite R21; unfold w64, d_obj, dobj_off; f_equal; lia|].
      split; [rewrite (o4_pres _ _ 22%bv HP) by o4_cs; rewrite R22; unfold w64, d_obj, dobj_off; reflexivity|].
      split; [rewrite Hv; exact Hv0|].
      split; [rewrite (o4_pres _ _ 23%bv HP) by o4_cs; rewrite (RG 23%bv) by (cbv; tauto); exact H23|].
      split; [rewrite (o4_pres _ _ 24%bv HP) by o4_cs; rewrite (RG 24%bv) by (cbv; tauto); exact H24|].
      rewrite (o4_pres _ _ 27%bv HP) by o4_cs. rewrite (RG 27%bv) by (cbv; tauto). exact H27.
Qed.

Definition o4_xs2 (cx : dcx) (Sg : list byte) (ow now nb : Z) : list word :=
  [w64 (u_at Sg 8 4); w64 (u_at Sg 12 1); w64 (u_at Sg 13 1); w64 (u_at Sg 14 1); w64 (u_at Sg 15 1);
   w64 (u_at Sg 16 1); w64 (u_at Sg 20 4); w64 ow; w64 now; w64 (d_cur cx nb)].

Ltac o4_ewx := rewrite o4_ew_x with (d := Z_to_bv 64 0) by (unfold o4_xs2; cbn; lia); unfold o4_xs2; reflexivity.
Ltac o4_ck v :=
  apply (YI04.chunk_ok_val SEGS _ _ _ _ _ _ v); [apply o4_sv_atom; o4_ewx | | lia | ];
  try (match goal with |- context [N.to_nat ?x] => let y := eval vm_compute in (N.to_nat x) in change (N.to_nat x) with y end).

Lemma o4_h2 : forall cx h i n now op nb fr len Sg W c,
  o4_ret cx h i n now op nb fr len Sg (EV_HEAD i + 1) (ACC_HEAD MT i + mo_malloc MT REC_MAX) W c ->
  SRr SEGS W c (r27 cx h i (nb - len) now nb fr len).
Proof.
intros cx h i n now op nb fr len Sg W c H.
destruct H as (fq & ly3 & S3 & regs & mem3 & md3 & k & acc & -> & Hf0 & Hbase & HJ & Hfrs & Hk & Hnev & Hmo & Hacc &
  T & T' & ow & HOC & H26 & HTl0 & HN8 & HON & How & H408 & H21 & H22 & H10 & H23 & H24 & H27).
pose proof HOC as (Hi & Hn & Hnow & Hop & Hop2 & HrL & Hsp0 & Hfrm & HSgl & HSg & HSf & H248 & H336 & H368 & H280 &
  Hlen & Hnb & HTl & HT & HTok & Hbody).
pose proof Hbody as (T0 & G0 & Lk0 & H0 & Hframe & _).
pose proof Hframe as (E & HdE & Hregs & Hflag & Hh216 & Hh152).
destruct (ob_A_range B cx ly3 S3 W mem3 md3 k HJ) as (HSr & HS16 & HAr & HA32).
assert (HctxD : d_ctx B MT XM_LIB RLO RHI tfib_K cx ly3 S3 W mem3 md3 k)
  by (split; [exact Hbase | split; [exact HJ | exact Hfrs]]).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HAr2 : 0 <= d_A cx < 2 ^ 64) by (unfold LLVMF_STK in HSr; lia).
destruct (slot_observe.new_facts T Sg ow now T' 1 HTl0 HSgl HN8 HON) as (_ & _ & _ & _ & NF).
destruct (slot_observe.new_fields Sg ow now HSgl) as (F0 & F8 & F12 & F13 & F14 & F15 & F16 & F20 & F24 & F32 & F40).
assert (UT : forall d (w : nat), 0 <= d -> d + Z.of_nat w <= 48 ->
  u_at T' (48 * n_of T + d) w = bytes_le_to_Z (sub (reac_disco_table_observe_c.new_entry Sg ow now) d w))
  by (intros d w Hd Hw; unfold u_at; rewrite NF by lia; reflexivity).
assert (VT : forall d (w : nat) v, 0 <= d -> d + Z.of_nat w <= 48 -> u_at T' (48 * n_of T + d) w = v ->
  val_mem SEGS (rd W mem3) (d_FB cx + (2160 + 48 * n_of T + d)) w v).
{ intros d w v Hd Hw <-. replace (d_FB cx + (2160 + 48 * n_of T + d)) with (d_obj cx OT + (48 * n_of T + d))
    by (unfold d_obj, dobj_off; lia).
  apply o4_val_mem_sub; [exact HT | lia | rewrite HTl; lia]. }
assert (VS : forall d (w : nat), 0 <= d -> d + Z.of_nat w <= 24 ->
  val_mem SEGS (rd W mem3) (d_FB cx + (2992 + d)) w (u_at Sg d w)).
{ intros d w Hd Hw. replace (d_FB cx + (2992 + d)) with (d_obj cx OS + d) by (unfold d_obj, dobj_off; lia).
  apply o4_val_mem_sub; [exact HSg | lia | rewrite HSgl; lia]. }
assert (RS : forall d (w : nat), 0 <= d -> d + Z.of_nat w <= 24 -> 0 <= u_at Sg d w < 2 ^ (8 * Z.of_nat w))
  by (intros d w Hd Hw; apply o4_u_range; [lia | rewrite HSgl; lia]).
assert (FC2 : Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb)) (rd W mem3) (d_FB cx))
  (o4_fcs (2160 + 48 * n_of T))).
{ unfold o4_fcs. repeat apply Forall_cons; try apply Forall_nil.
  - o4_ck (u_at Sg 8 4); [exact (RS 8 4%nat ltac:(lia) ltac:(lia)) | apply VT; [lia | lia | rewrite UT, F8 by lia; reflexivity]].
  - o4_ck (u_at Sg 12 1); [exact (RS 12 1%nat ltac:(lia) ltac:(lia)) | apply VT; [lia | lia | rewrite UT, F12 by lia; reflexivity]].
  - o4_ck (u_at Sg 13 1); [exact (RS 13 1%nat ltac:(lia) ltac:(lia)) | apply VT; [lia | lia | rewrite UT, F13 by lia; reflexivity]].
  - o4_ck (u_at Sg 14 1); [exact (RS 14 1%nat ltac:(lia) ltac:(lia)) | apply VT; [lia | lia | rewrite UT, F14 by lia; reflexivity]].
  - o4_ck (u_at Sg 15 1); [exact (RS 15 1%nat ltac:(lia) ltac:(lia)) | apply VT; [lia | lia | rewrite UT, F15 by lia; reflexivity]].
  - o4_ck (u_at Sg 16 1); [exact (RS 16 1%nat ltac:(lia) ltac:(lia)) | apply VT; [lia | lia | rewrite UT, F16 by lia; reflexivity]].
  - o4_ck (u_at Sg 20 4); [exact (RS 20 4%nat ltac:(lia) ltac:(lia)) | apply VT; [lia | lia | rewrite UT, F20 by lia; reflexivity]].
  - o4_ck ow; [change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia | apply VT; [lia | lia | rewrite UT, F24 by lia]].
    destruct How as [Hw|Hw]; rewrite Hw; reflexivity.
  - o4_ck now; [exact Hnow | apply VT; [lia | lia | rewrite UT, F32 by lia; apply o4_u_le; exact Hnow]].
  - o4_ck now; [exact Hnow | apply VT; [lia | lia | rewrite UT, F40 by lia; apply o4_u_le; exact Hnow]].
  - o4_ck (u_at Sg 8 4); [exact (RS 8 4%nat ltac:(lia) ltac:(lia)) | exact (VS 8 4%nat ltac:(lia) ltac:(lia))].
  - o4_ck (u_at Sg 12 1); [exact (RS 12 1%nat ltac:(lia) ltac:(lia)) | exact (VS 12 1%nat ltac:(lia) ltac:(lia))].
  - o4_ck (u_at Sg 13 1); [exact (RS 13 1%nat ltac:(lia) ltac:(lia)) | exact (VS 13 1%nat ltac:(lia) ltac:(lia))].
  - o4_ck (u_at Sg 14 1); [exact (RS 14 1%nat ltac:(lia) ltac:(lia)) | exact (VS 14 1%nat ltac:(lia) ltac:(lia))].
  - o4_ck (u_at Sg 15 1); [exact (RS 15 1%nat ltac:(lia) ltac:(lia)) | exact (VS 15 1%nat ltac:(lia) ltac:(lia))].
  - o4_ck (u_at Sg 16 1); [exact (RS 16 1%nat ltac:(lia) ltac:(lia)) | exact (VS 16 1%nat ltac:(lia) ltac:(lia))].
  - o4_ck (u_at Sg 20 4); [exact (RS 20 4%nat ltac:(lia) ltac:(lia)) | exact (VS 20 4%nat ltac:(lia) ltac:(lia))]. }
assert (AC2 : Forall (YP09.chunk_ok SEGS (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb)) (rd W mem3) (d_A cx)) o4_acs).
{ unfold o4_acs. repeat apply Forall_cons; try apply Forall_nil.
  - apply (YI04.chunk_ok_val SEGS _ _ _ _ 8 _ (d_cur cx nb mod 2 ^ 64));
      [ | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); apply Z.mod_pos_bound; lia | lia | ].
    + apply o4_sv_atom. rewrite o4_ew_x with (d := Z_to_bv 64 0) by (unfold o4_xs2; cbn; lia). unfold o4_xs2. cbn [nth Nat.sub].
      unfold w64. apply o4_w64_mod.
    + intros j Hj. rewrite (H248 j Hj). do 2 f_equal. unfold YO0f.le_byte.
      change (8 * Z.of_nat (N.to_nat 8)) with 64. change (8 * Z.of_nat 8) with 64. rewrite Zmod_mod. reflexivity.
  - o4_ck now; [exact Hnow | exact (proj2 Hsp0)].
  - o4_ck ow; [change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | exact H408]. }
pose proof (o4_regs_ok B cx E regs (o4_xs2 cx Sg ow now nb) HdE HrL HAr2) as RO2.
assert (EW516 : ew (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb)) 516 = Z_to_bv 64 (d_FB cx)).
{ rewrite d_env_old by (unfold AT_FL; lia). destruct HdE as (_ & _ & _ & _ & EF & _). exact EF. }
assert (EW570 : ew (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb)) 570 = Z_to_bv 64 ow) by o4_ewx.
assert (EW572 : ew (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb)) 572 = Z_to_bv 64 (d_cur cx nb)) by o4_ewx.
assert (SV541 : sv_denot (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb)) (SOff 541 0) =
  sv_denot (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb)) (SLit 0)).
{ pose proof (RO2 10%bv) as R. o4_rr R. rewrite H10 in R. rewrite <- R. reflexivity. }
assert (HEI : img_env VAL A_LIM (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb))).
{ destruct HdE as (_ & _ & HI & _). intros a Ha. unfold d_env. rewrite ew_havoc_old by (unfold A_LIM, AT_FL in *; lia). exact (HI a Ha). }
assert (SHOK : sh_ok SEGS (SOff 32 0) [] (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb)) (rd W mem3)) by constructor.
pose (RUN := paj_run (fx := fq) B LAWS).
pose proof (paj_run_to (fx := fq) B LAWS) as RUNTO.
pose proof (paj_branch (fx := fq) (PI := PI)) as BR.
assert (MP : forall x, mem3 x = mem3 x) by reflexivity.
unfold cfg_at. change (w64 (BASE + 0x1bc0)) with (Z_to_bv 64 (BASE + 0x1bc0)).
assert (R21 : getr regs 21%bv = sv_denot (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb)) (SOff 516 (2160 + 48 * n_of T))).
{ cbn [sv_denot]. rewrite EW516, w64_add_w, H21. unfold w64, d_obj, dobj_off. f_equal; lia. }
assert (R22 : getr regs 22%bv = sv_denot (d_env cx E (obs_vals regs ++ o4_xs2 cx Sg ow now nb)) (SOff 516 2992)).
{ cbn [sv_denot]. rewrite EW516, w64_add_w, H22. unfold w64, d_obj, dobj_off. reflexivity. }
assert (Hm : n_of T = 0 \/ n_of T = 1 \/ n_of T = 2 \/ n_of T = 3 \/ n_of T = 4 \/ n_of T = 5 \/ n_of T = 6 \/ n_of T = 7) by lia.
destruct Hm as [Hm|[Hm|[Hm|[Hm|[Hm|[Hm|[Hm|Hm]]]]]]]; rewrite Hm in FC2, R21.
all: lazymatch goal with
  | FC2 : Forall _ (o4_fcs ?e) |- _ =>
    let HS := fresh "HS" in
    pose proof (d_seat B MT XM_LIB RLO RHI tfib_K LAWS TL fq cx dsh_rec ly3 S3 W regs mem3 md3 k E 0x1bc0 obs_sr _
      o4_acs (o4_fcs e) [] (d_facts [] []) HctxD HdE Hregs Hflag RO2
      (d_facts_ok B MT XM_LIB RLO RHI tfib_K LAWS cx ly3 S3 W mem3 md3 k E _ [] [] HctxD HdE I I)
      AC2 FC2 (Forall_nil _) I (Forall_nil _) ltac:(vm_compute; reflexivity)) as HS;
    unfold ss_d in HS;
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let HS2 := fresh "HS" in
      pose proof (st_ok_pi_set_reg Ex ssx msx 21%bv (SOff 516 e) HS ltac:(discriminate) R21) as HS2;
      clear HS; rename HS2 into HS; norm_ss HS
    end;
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx ?msx =>
      let HS2 := fresh "HS" in
      pose proof (st_ok_pi_set_reg Ex ssx msx 22%bv (SOff 516 2992) HS ltac:(discriminate) R22) as HS2;
      clear HS; rename HS2 into HS; norm_ss HS
    end;
    ro_base HS 516%nat; ro_base HS 529%nat; ro_base HS 60%nat
  end;
  o4_run RUN;
  psrr_branch_tok RUN BR HS SHOK OBspan;
  [ exfalso; rewrite (o4_br_ne_false _ (SOff 541 0) (SLit 0)) in Hc; [discriminate Hc | exact SV541]
  | clear Hc; o4_run RUN;
    psrr_branch_tok RUN BR HS SHOK OBspan;
    [ exfalso; rewrite (o4_br_ne_false _ (SExt true 32 (SOff 570 0)) (SOff 570 0)) in Hc; [discriminate Hc|];
      rewrite (o4_sv_sext32 _ 570 _ EW570 ltac:(lia)), (o4_sv_atom _ 570 _ EW570);
      destruct How as [Hw|Hw]; rewrite Hw; reflexivity
    | clear Hc; o4_runto RUNTO 6984;
      repeat rewrite wvb_collapse in HJ;
      apply SRr_ret;
      lazymatch goal with HS : st_ok_pi _ _ ?Ex ?ss (restrict _ ?ms) |- _ =>
        assert (RG : forall r : bv 5, In r [2; 3; 4; 8; 9; 18; 20; 23; 24; 25; 26; 27]%bv ->
          getr (ms_regs ms) r = getr regs r)
          by (intros r Hr; rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms r HS), (RO2 r); cbv [In] in Hr;
              repeat (destruct Hr as [<-|Hr]; [f_equal; vm_compute; reflexivity|]); destruct Hr);
        assert (R22f : getr (ms_regs ms) 22%bv = w64 (d_obj cx OS))
          by (rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms 22%bv HS);
              match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
              cbn [sv_denot]; rewrite EW516, w64_add_w; reflexivity);
        assert (R14f : getr (ms_regs ms) 14%bv = w64 (d_cur cx nb))
          by (rewrite (st_ok_pi_restrict_reg (w_H W) _ _ ms 14%bv HS);
              match goal with |- context [sr_get ?sr ?r] => let v := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with v end;
              exact (o4_sv_atom _ 572 _ EW572));
        apply (o4_land fq cx h i now nb fr len n ly3 S3 W mem3 _ k acc E _ ss ms Hf0 Hbase HJ Hfrs Hk Hnev Hmo Hacc HdE HS
          ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) MP
          Hi Hnow Hlen Hnb Hbody Hsp0 Hfrm);
        [ destruct HrL as (Hsp & Hgp & Htp & H8 & H9 & H18 & H20 & H25); unfold d_rL, spZ in *;
          rewrite (RG 2%bv), (RG 3%bv), (RG 4%bv), (RG 8%bv), (RG 9%bv), (RG 18%bv), (RG 20%bv), (RG 25%bv) by (cbv; tauto);
          repeat split; assumption
        | exact R14f
        | rewrite (RG 24%bv) by (cbv; tauto); exact H24
        | rewrite (RG 23%bv) by (cbv; tauto); exact H23
        | rewrite (RG 27%bv) by (cbv; tauto); exact H27
        | exact R22f
        | rewrite (RG 26%bv) by (cbv; tauto); exact H26 ]
      end ] ].
Qed.

Theorem ob_s10 : ob_seg10r B MT XM_LIB RLO RHI tfib_K.
Proof.
intros cx h i n now op nb fr len Sg W c H.
eapply SRr_bind; [exact (o4_h1 cx h i n now op nb fr len Sg W c H)|].
intros W' c' _ [HR|HR]; [apply SRr_ret; exact HR | exact (o4_h2 cx h i n now op nb fr len Sg W' c' HR)].
Qed.
End h.
End f.
End d.
