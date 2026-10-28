(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OssFuzzTheorems.cgif.cgif_file_fuzzer.images Require Import Asan.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO0d YO0f.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0f YG0v YG0n YG0d YCe5.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD1v AD1y AD26 AD24.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YM05.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import ACeg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AD21 AD25 AD23 AD2h AD1w AD2f AD2b AD2g AD1s AD2c.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib Require Import YO05 YO09 YO06 YO01.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
Definition B0_r0 : YP09.region := Eval vm_compute in (nth 0 (ss_mem sB0) WIN208).
Definition B1_r0 : YP09.region := Eval vm_compute in (nth 0 (ss_mem sB1) WIN208).
Definition B0_r5 : smem := Eval vm_compute in (skipn 36 (ss_mem sB0)).
Definition B1_r5 : smem := Eval vm_compute in (skipn 36 (ss_mem sB1)).
Lemma sB0_split : ss_mem sB0 = B0_r0 :: firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_B ++ B0_r5. Proof. vm_compute. reflexivity. Qed.
Lemma sB1_split : ss_mem sB1 = B1_r0 :: firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_B ++ B1_r5. Proof. vm_compute. reflexivity. Qed.
Lemma sPE0_split : ss_mem sPE0 = B0_r0 :: firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_E ++ B0_r5. Proof. vm_compute. reflexivity. Qed.
Lemma sPE1_split : forall k, ss_mem (sPE1 k) = B1_r0 :: firstn 2 (skipn 1 (ss_mem S_Pm)) ++ IMG_E ++ B1_r5. Proof. intros k. vm_compute. reflexivity. Qed.
Definition TRFc : YP09.region := Eval vm_compute in TRF.
Lemma L_pieces_unfold : L_piecesC = [ [WIN208; TRFc] ] ++ map (fun r => [r]) (firstn 2 (skipn 1 (ss_mem S_Pm)))
++ map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) IMG_E ++ map (fun _ => @nil YP09.region) B1_r5.
Proof. vm_compute. reflexivity. Qed.
Lemma IMG_B_lohi : forallb (fun r => r_lo r <=? r_hi r) IMG_B = true. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_E_lohi : forallb (fun r => r_lo r <=? r_hi r) IMG_E = true. Proof. vm_compute. reflexivity. Qed.
Definition img_cells (rs : smem) : list (Z * Z) :=
flat_map (fun r => match r_base r with
| None => flat_map (fun c => match YP09.c_val c with CImg _ => [(YP09.c_off c, c_len c)] | _ => [] end) (r_chunks r)
| Some _ => [] end) rs.
Definition IMG_CELLS : list (Z * Z) := Eval vm_compute in img_cells IMG_B.
Lemma IMG_CELLS_eq : img_cells IMG_B = IMG_CELLS. Proof. vm_compute. reflexivity. Qed.
Lemma IMG_CELLS_eqE : img_cells IMG_E = IMG_CELLS. Proof. vm_compute. reflexivity. Qed.
Definition jump_cover (cells : list (Z * Z)) (a : Z) : Z :=
fold_right (fun c acc => if ((fst c <=? a) && (a <? fst c + snd c))%bool then Z.max acc (fst c + snd c) else acc) a cells.
Fixpoint cover_from (fuel : nat) (cells : list (Z * Z)) (a hi : Z) : bool :=
match fuel with
| O => false
| S f => if hi <=? a then true else let a' := jump_cover cells a in if a' <=? a then false else cover_from f cells a' hi
end.
Lemma jump_cover_spec : forall cells a, jump_cover cells a = a \/ exists c, In c cells /\ fst c <= a < fst c + snd c /\ jump_cover cells a <= fst c + snd c.
Proof.
intros cells a. induction cells as [|c cells IH]; cbn; [left; reflexivity|].
fold (jump_cover cells a).
destruct (andb (fst c <=? a) (a <? fst c + snd c)) eqn:Eb.
- apply andb_prop in Eb as [E1 E2]. apply Z.leb_le in E1. apply Z.ltb_lt in E2.
destruct (Z.le_ge_cases (jump_cover cells a) (fst c + snd c)).
+ right. exists c. split; [left; reflexivity|]. split; [lia|]. lia.
+ destruct IH as [IH | (c' & Hin & Hc' & Hj)]; [left; lia |]. right. exists c'. split; [right; exact Hin|]. split; [exact Hc'|]. lia.
- destruct IH as [IH | (c' & Hin & Hc' & Hj)]; [left; exact IH |]. right. exists c'. split; [right; exact Hin|]. split; [exact Hc'|]. exact Hj.
Qed.
Lemma cover_from_sound : forall fuel cells a hi, cover_from fuel cells a hi = true ->
forall x, a <= x < hi -> exists c, In c cells /\ fst c <= x < fst c + snd c.
Proof.
induction fuel as [|fuel IH]; cbn; intros cells a hi Hc x Hx; [discriminate|].
destruct (Z.leb_spec hi a); [lia|]. destruct (Z.leb_spec (jump_cover cells a) a) as [|Hgt]; [discriminate|].
destruct (Z.lt_ge_cases x (jump_cover cells a)) as [Hlt|Hge].
- destruct (jump_cover_spec cells a) as [Heq | (c & Hin & Hca & Hj)]; [lia|]. exists c. split; [exact Hin | lia].
- exact (IH cells _ hi Hc x ltac:(lia)).
Qed.
Definition RO_CELLS : list (Z * Z) := IMG_CELLS ++ Tfib_owned_static ++ [(TFIB_ERRNO, 4)].
Lemma ro_cover_chk : cover_from 200 RO_CELLS 0x10000 0x9d000 = true /\ cover_from 200 RO_CELLS 0x9da38 0x9eca8 = true.
Proof. vm_compute. split; reflexivity. Qed.
From OssFuzzTheorems.Proofs.cgif.cgif_file_fuzzer.lib.A Require Import AE2k AD1u.
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Definition run_QM_tfa (B : asyms) : Prop :=
forall (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (ws : list word)
(W : world tfibsegs) (ms : machine_state) (md : Model) (ly : alayout) (S : astate) (a0 p data : list byte) (pb : sptr) (cap : Z),
in_argv inp = [a0; p] -> valid_sp sp -> valid_argv [a0; p] -> valid_envp (in_envp inp) -> valid_fs (in_fs inp) ->
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data -> 0 < payload_len data ->
let E3 := E_P (edset (havoc (YP08.E0 sp [a0; p] (in_envp inp) xw xd) K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at B (if config_len data =? 0 then sPM0 else sPM1 (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S pb cap ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes tfibsegs (mkCfg ms md) (run_shape (payload data) (calls data) (in_fs inp)).
Section g.
Variable B : asyms.
Hypothesis HB : TfibSyms B.
Hypothesis ARL : AR_laws tfibsegs B.
Variable xst : nat -> (word -> bool) -> (word -> option byte) -> Prop.
Hypothesis LOOPL : loop_L_x B xst.
Hypothesis RUNQM : run_QM_tfa B.
Variables (sp : word) (inp : ProcInput) (xw : nat -> word) (xd : nat -> list byte) (a0 p : list byte).
Hypothesis Hargv : in_argv inp = [a0; p].
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv [a0; p].
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hvfs : valid_fs (in_fs inp).
#[local] Notation EL := (YP08.E0 sp [a0; p] (in_envp inp) xw xd).
#[local] Notation usp := (bv_unsigned sp).
#[local] Notation envp := (in_envp inp).
Let HWXi : wx_segs_nowrap tfibsegs := Hwx_tfa.
Lemma U_pl00 : forall E data d0 d1 rest, ed E 2 = data -> data = d0 :: d1 :: rest ->
bv_unsigned (ew E A_LEN) = dlen data -> 6 + config_len data <= dlen data -> dlen data < 2 ^ 62 -> U E sv_pl00 = payload_len data.
Proof.
intros E data d0 d1 rest Hd Ed E42 Hok Hhi. unfold sv_pl00. rewrite !U_add0. unfold sv_pl.
rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SAlu. cbn [zalu_raw]. rewrite U_SOff, U_SLit, E42, Z.add_0_r.
rewrite (U_cl E d0 d1 rest) by (rewrite Hd; exact Ed). rewrite <- Ed. pose proof (config_len_bound data) as Hcl. unfold dlen in *.
rewrite (zcanon_id (Z.of_nat (length data))) by (unfold M64; lia). rewrite (zcanon_id (Z.of_nat (length data) - config_len data)) by (unfold M64; lia).
unfold zcanon at 2. change ((-6) mod M64) with (M64 - 6). unfold zcanon, M64.
replace (Z.of_nat (length data) - config_len data + (2 ^ 64 - 6)) with (Z.of_nat (length data) - config_len data - 6 + 1 * 2 ^ 64) by lia.
rewrite Z_mod_plus_full. rewrite Z.mod_small by lia. unfold payload_len, dlen, HDR_MIN. lia.
Qed.
Lemma img_cells_view : forall (I : smem) E (H : word -> bool) m rs clo cl, img_cells I = IMG_CELLS ->
mem_ok tfibsegs E (mrestrict H m) rs -> (forall r, In r I -> In r rs) -> In (clo, cl) IMG_CELLS ->
forall a, clo <= a < clo + cl -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof.
intros I E H m rs clo cl HI (_ & Hok & _) Hsub Hin a Ha. rewrite <- HI in Hin. unfold img_cells in Hin.
apply in_flat_map in Hin as (r & Hr & Hin).
pose proof (proj1 (Forall_forall _ _) Hok _ (Hsub r Hr)) as (_ & _ & _ & HC).
destruct (r_base r) as [n|] eqn:Eb; [destruct Hin|]. cbn [base_val] in HC.
apply in_flat_map in Hin as (c & Hc & Hin). destruct (YP09.c_val c) as [w v|zl|il|d s0 dl] eqn:Ev; try (destruct Hin; fail); [].
destruct Hin as [Heq|[]]. injection Heq as E1 E2.
pose proof (proj1 (Forall_forall _ _) HC _ Hc (a - clo)) as Hck. rewrite E2, E1, Ev in Hck.
destruct (Hck ltac:(lia)) as (b & Hb1 & Hb2). cbn [cbyte] in Hb1. unfold img_byte in Hb1.
replace (0 + clo + (a - clo)) with a in Hb1, Hb2 by lia. unfold aview. rewrite Hb2, <- Hb1. reflexivity.
Qed.
Lemma img_facts_of : forall (I : smem) E (H : word -> bool) m rs, img_cells I = IMG_CELLS ->
mem_ok tfibsegs E (mrestrict H m) rs -> (forall r, In r I -> In r rs) ->
stdout_img H m /\ arodata_ok B (aview tfibsegs H m).
Proof.
intros I E H m rs HI HM Hsub. split.
- intros a Ha. unfold STDOUT_LO, STDOUT_HI in Ha. apply (img_cells_view I E H m rs 664880 832 HI HM Hsub); [vm_compute; tauto | lia].
- intros a Hrin Hno Herr.
assert (Hro : 0x10000 <= a < 0x9d000 \/ 0x9da38 <= a < 0x9eca8).
{ destruct Hrin as [(s & Hs & Hws & Hrg) | Hrel]; [left | right; exact Hrel].
cbn in Hs. destruct Hs as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hws, Hrg; try discriminate Hws; lia. }
assert (Hc : exists c, In c RO_CELLS /\ fst c <= a < fst c + snd c).
{ destruct Hro as [Hro|Hro]; [exact (cover_from_sound _ _ _ _ (proj1 ro_cover_chk) a Hro) | exact (cover_from_sound _ _ _ _ (proj2 ro_cover_chk) a Hro)]. }
destruct Hc as ([clo cl] & Hin & Hca). cbn [fst snd] in Hca. unfold RO_CELLS in Hin.
apply in_app_iff in Hin as [Hin | Hin]; [exact (img_cells_view I E H m rs clo cl HI HM Hsub Hin a Hca)|].
apply in_app_iff in Hin as [Hin | [Heq | []]].
+ exfalso. apply Hno. rewrite (ts_owned B HB). apply Exists_exists. exists (clo, cl). split; [exact Hin | unfold in_zr; cbn; lia].
+ exfalso. apply Herr. rewrite (ts_errno B HB). injection Heq as <- <-. exact Hca.
Qed.
Lemma sB_img_facts : forall (c0 : bool) E (H : word -> bool) m,
mem_ok tfibsegs E (mrestrict H m) (ss_mem (if c0 then sB0 else sB1)) ->
stdout_img H m /\ arodata_ok B (aview tfibsegs H m).
Proof.
intros c0 E H m HM. apply (img_facts_of IMG_B E H m _ IMG_CELLS_eq HM).
intros r Hr. destruct c0; [rewrite sB0_split | rewrite sB1_split]; right; apply in_app_iff; right; apply in_app_iff; left; exact Hr.
Qed.
Lemma sPE_img_facts : forall (c0 : bool) k E (H : word -> bool) m,
mem_ok tfibsegs E (mrestrict H m) (ss_mem (if c0 then sPE0 else sPE1 k)) ->
stdout_img H m /\ arodata_ok B (aview tfibsegs H m).
Proof.
intros c0 k E H m HM. apply (img_facts_of IMG_E E H m _ IMG_CELLS_eqE HM).
intros r Hr. destruct c0; [rewrite sPE0_split | rewrite sPE1_split]; right; apply in_app_iff; right; apply in_app_iff; left; exact Hr.
Qed.
Lemma refines_B : forall (c0 : bool) k E3 (m : word -> option byte),
refines E3 m (ss_mem (if c0 then sPE0 else sPE1 k)) L_piecesC.
Proof.
intros c0 k E3 m. rewrite L_pieces_unfold.
assert (IMG : refines E3 m IMG_E (map (fun r => flat_map (clip_out SOBUF_LO SOBUF_HI) (clip_out STDOUT_LO STDOUT_HI r)) IMG_E)).
{ apply refines_map. intros r Hr. pose proof (proj1 (forallb_forall _ _) IMG_E_lohi r Hr) as Hlh. cbn beta in Hlh. apply Z.leb_le in Hlh.
apply flat_map_pieces_ok; [apply clip_out_ok; [unfold STDOUT_LO, STDOUT_HI; lia | exact Hlh] |].
intros q _ Hq. apply clip_out_ok; [unfold SOBUF_LO, SOBUF_HI; lia | exact Hq]. }
#[local] Ltac r0_piece Hr :=
eapply region_ok_sub; [| cbn; lia | exact Hr]; split; [reflexivity|]; split; [cbn; lia|]; split; [cbn; lia|];
split; [cbn; first [left; lia | right; lia] | intros c Hc; cbn in Hc |- *; tauto].
destruct c0; [rewrite sPE0_split | rewrite sPE1_split];
(apply refines_cons;
[ intros Hr; constructor; [r0_piece Hr | constructor; [r0_piece Hr | constructor]]
| constructor; [unfold ext_in; cbn; repeat split; first [reflexivity | lia] | constructor; [unfold ext_in; cbn; repeat split; first [reflexivity | lia] | constructor]]
| cbn [pairwise_disjoint all_disjoint]; unfold extent_disjoint; cbn [base_val r_base r_lo r_hi WIN208 TRFc]; split; [split; [left; lia | exact I] | split; exact I]
| apply refines_app; [apply refines_single | apply refines_app; [exact IMG |]] ]);
[apply (refines_drop_each E3 m B0_r5) | apply (refines_drop_each E3 m B1_r5)].
Qed.
Lemma pe_to_L : forall (c0 : bool) (k : Z) E3 (W : world tfibsegs) ms (n : Z),
st_ok tfibsegs E3 (if c0 then sPE0 else sPE1 k) (restrict (w_H W) ms) ->
U E3 sv_pl00 = n -> 0 <= n <= 2 ^ 26 -> 1 <= k <= 4 -> (c0 = true -> k = 1) ->
let E' := E_L E3 (ms_regs ms) in
st_ok tfibsegs E' S_L (restrict (w_H W) ms)
/\ bv_unsigned (ew E' 162) = n /\ bv_unsigned (ew E' 163) = A_EMPTY_tfa /\ bv_unsigned (ew E' 164) = 0 /\ bv_unsigned (ew E' 166) = k.
Proof.
intros c0 k E3 W ms n HS Hn Hnb Hk Hc0 E'.
set (ss := if c0 then sPE0 else sPE1 k) in *. set (regs := ms_regs ms) in *.
pose proof sPE0_facts as F0. pose proof (sPE1_facts k) as F1.
assert (R : forall r v, (sr_get (ss_regs sPE0) r = v /\ sr_get (ss_regs (sPE1 k)) r = v) \/ (c0 = true /\ sr_get (ss_regs sPE0) r = v) \/ (c0 = false /\ sr_get (ss_regs (sPE1 k)) r = v) ->
getr regs r = sv_denot E3 v).
{ intros r v Hv. subst regs. rewrite (st_ok_restrict_reg tfibsegs (w_H W) E3 ss ms r HS). subst ss.
destruct c0; (destruct Hv as [[H0 H1]|[[Hc H']|[Hc H']]]; [| | ]); try discriminate Hc; rewrite ?H0, ?H1, ?H'; reflexivity. }
assert (R8 : getr regs 8%bv = sv_denot E3 sv_pl00) by (apply R; left; tauto).
assert (R9 : getr regs 9%bv = w64 A_EMPTY_tfa) by (rewrite (R 9%bv (SLit A_EMPTY_tfa)) by (left; tauto); reflexivity).
assert (R10 : getr regs 10%bv = w64 A_EMPTY_tfa) by (rewrite (R 10%bv (SLit A_EMPTY_tfa)) by (left; tauto); reflexivity).
assert (R11 : getr regs 11%bv = sv_denot E3 (add0 sv_pl00)) by (apply R; left; tauto).
assert (R18 : getr regs 18%bv = w64 0) by (rewrite (R 18%bv (SLit 0)) by (left; tauto); reflexivity).
assert (R20 : getr regs 21%bv = w64 k).
{ destruct c0; [rewrite (Hc0 eq_refl); rewrite (R 21%bv (SLit 1)) by (right; left; tauto) | rewrite (R 21%bv (SLit k)) by (right; right; tauto)]; reflexivity. }
assert (R8_11 : getr regs 11%bv = getr regs 8%bv) by (rewrite R8, R11, !denot_lit_U, U_add0; reflexivity).
assert (NEW : forall i r, (i < 18)%nat -> nth i L_srcs 0%bv = r -> ew E' (K_L + i) = getr regs r).
{ intros i r Hi <-. subst E'. unfold E_L. rewrite (ew_havoc_new E3 K_L _ i (getr regs 0%bv)) by (rewrite length_map; exact Hi). apply map_nth. }
assert (V61 : bv_unsigned (ew E' 162) = n).
{ change 162%nat with (K_L + 0)%nat. rewrite (NEW 0%nat 8%bv) by (cbn; first [lia | reflexivity]). rewrite R8. exact Hn. }
assert (V62 : bv_unsigned (ew E' 163) = A_EMPTY_tfa).
{ change 163%nat with (K_L + 1)%nat. rewrite (NEW 1%nat 9%bv) by (cbn; first [lia | reflexivity]). rewrite R9. apply u64_lit. unfold A_EMPTY_tfa; lia. }
assert (V63 : bv_unsigned (ew E' 164) = 0).
{ change 164%nat with (K_L + 2)%nat. rewrite (NEW 2%nat 18%bv) by (cbn; first [lia | reflexivity]). rewrite R18. apply u64_lit. lia. }
assert (V65 : bv_unsigned (ew E' 166) = k).
{ change 166%nat with (K_L + 4)%nat. rewrite (NEW 4%nat 21%bv) by (cbn; first [lia | reflexivity]). rewrite R20. apply u64_lit. lia. }
split; [| repeat split; assumption].
pose proof (st_ok_mem_ok tfibsegs E3 ss _ HS) as HM0. cbn [restrict ms_mem] in HM0.
assert (HM1 : mem_ok tfibsegs E3 (mrestrict (w_H W) (ms_mem ms)) L_mem).
{ rewrite <- (proj2 L_piecesC_eq). apply (mem_ok_refine E3 _ (ss_mem (if c0 then sPE0 else sPE1 k))).
- subst ss. exact HM0.
- apply refines_B.
- rewrite (proj2 L_piecesC_eq). exact (proj1 L_mem_wf). }
assert (HM2 : mem_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms)) L_mem).
{ apply (mem_ok_agree tfibsegs K_L E3); [| exact (proj1 (proj2 L_mem_wf)) | exact HM1].
split; [| subst E'; reflexivity]. intros j Hj. subst E'. unfold E_L. rewrite ew_havoc_old by exact Hj. reflexivity. }
pose proof sPE_mem as (_ & _ & P0 & P1 & _).
assert (Hpc : ss_pc ss = A_LLVMF) by (subst ss; destruct c0; [exact P0 | exact (P1 k)]).
unfold S_L. rewrite <- Hpc.
apply (st_ok_reabs tfibsegs LT162 E3 E' ss (restrict (w_H W) ms) L_regs L_mem L_facts HS).
- split; [| intros d _; subst E'; reflexivity]. intros j Hj. unfold LT162 in Hj. apply Nat.ltb_lt in Hj. subst E'. unfold E_L. apply ew_havoc_old. exact Hj.
- subst ss. destruct c0; [exact (proj1 reabs_chk_PE) | exact (proj2 reabs_chk_PE k)].
- cbn [ms_regs restrict]. fold regs.
apply Forall_forall. intros [r j] Hin. vm_compute in Hin. cbn [fst snd].
#[local] Ltac oneL NEW i := rewrite <- (NEW i); [apply f_equal; reflexivity | cbn; lia | apply bv_eq; vm_compute; reflexivity].
repeat (destruct Hin as [Heq|Hin]; [injection Heq as <- <-;
first [ oneL NEW 0%nat | oneL NEW 1%nat | oneL NEW 2%nat | oneL NEW 3%nat | oneL NEW 4%nat | oneL NEW 5%nat | oneL NEW 6%nat | oneL NEW 7%nat
| oneL NEW 8%nat | oneL NEW 9%nat | oneL NEW 10%nat | oneL NEW 11%nat | oneL NEW 12%nat | oneL NEW 13%nat | oneL NEW 14%nat
| oneL NEW 15%nat | oneL NEW 16%nat | oneL NEW 17%nat
|   transitivity (getr regs 9%bv); [oneL NEW 1%nat | rewrite R9; rewrite <- R10; apply f_equal; apply bv_eq; vm_compute; reflexivity]
|   transitivity (getr regs 8%bv); [oneL NEW 0%nat | rewrite <- R8_11; apply f_equal; apply bv_eq; vm_compute; reflexivity] ] |]).
destruct Hin.
- rewrite L_fact_obls_eq.
constructor; [| constructor; [| constructor; [| constructor; [| constructor]]]];
unfold afact_ok; cbn [af_lo af_hi af_al2 fst snd fact_n fact_p fact_q fact_r]; rewrite ?V61, ?V62, ?V63, ?V65;
change (2 ^ 0) with 1; rewrite ?Z.mod_1_r; unfold A_EMPTY_tfa; repeat split; try reflexivity; lia.
- exact HM2.
Qed.
Lemma pe_run : forall (c0 : bool) k E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond (sQ c0 k) cond_PL0) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st (sQ c0 k) (if c0 then sPE0 else sPE1 k) E W (ms_mem ms) md).
Proof.
intros c0 k E W ms md HS. pose proof HWXi as HWX. pose proof sPE_eq as [Q0 Q1].
destruct c0; unfold sQ in *; [rewrite <- Q0 | rewrite <- (Q1 k)]; unfold sPE, sQ; srr_run_with tfibtbl_lp_ok HS;
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]);
(split; [exact HS|]); split; first [exact HF | exact HFr].
Qed.
Theorem tfib_run_Q_empty : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data -> payload_len data = 0 ->
let E3 := E_P (edset (havoc EL K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at B (sQ (config_len data =? 0) (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S pb cap ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes tfibsegs (mkCfg ms md) (run_shape (payload data) (calls data) (in_fs inp)).
Proof.
intros ws W ms md ly S data pb cap Hlk Hok Hpl0 E3 HT E60.
destruct HT as (HS & E41 & E42 & HR & HAI & HAR & HTOP & Hbl & Hnev & Hcap & HLc & HBLK & Hfs & Hfds & Hminv & HFI).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (buf := sptr_addr B ly pb) in *. set (c0 := config_len data =? 0) in *. set (k := Z.of_nat (calls data)) in *.
pose proof (config_len_bound data) as Hcl. pose proof (calls_bound data) as Hcb. unfold dlen in *.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (al_blocks _ _ ARL ly S W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (E3_0 : bv_unsigned (ew E3 0) = usp) by (subst E3; rewrite E_P_old by lia; cbn [ew edset]; rewrite ew_havoc_old by (unfold K_M1; lia); reflexivity).
assert (Ed2 : ed E3 2 = data) by (subst E3; rewrite E_P_ed by lia; reflexivity).
destruct (list_len3 data ltac:(lia)) as (d0 & d1 & d2 & rest & Ed).
assert (UPL : U E3 sv_pl00 = payload_len data).
{ apply (U_pl00 E3 data d0 d1 (d2 :: rest) Ed2 Ed); unfold dlen; [exact E42 | lia | lia]. }
assert (Hk : 1 <= k <= 4) by (subst k; lia).
assert (Hk1 : c0 = true -> k = 1).
{ subst c0 k. intros Hz. unfold calls, cfg_byte. rewrite Hz. reflexivity. }
assert (HS1 : st_ok tfibsegs E3 (add_cond (sQ c0 k) cond_PL0) (restrict (w_H W) ms)).
{ apply (st_ok_add_cond tfibsegs E3 (sQ c0 k) _ BC_EQ sv_pl00 (SLit 0) HS). rewrite branch_eq_U, UPL, U_SLit, Hpl0. reflexivity. }
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (pe_run c0 k E3 W ms md HS1) HAI).
intros W0 c' _ HAI1 (-> & ms1 & mat1 & -> & HS2 & HF1 & HFr1). cbn [cfg_model] in HAI1.
pose proof (pe_to_L c0 k E3 W ms1 (payload_len data) HS2 UPL ltac:(unfold payload_len, dlen, HDR_MIN; lia) Hk Hk1) as (HSL & V61 & V62 & V63 & V65).
set (E4 := E_L E3 (ms_regs ms1)) in *.
assert (E4old : forall j, (j < K_L)%nat -> ew E4 j = ew E3 j) by (intros j Hj; subst E4; unfold E_L; apply ew_havoc_old; exact Hj).
pose proof (st_ok_mem_ok tfibsegs E3 _ _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
pose proof HM2 as HMB.
destruct (sPE_img_facts c0 k E3 (w_H W) (ms_mem ms1) HMB) as [HIMG HRO].
assert (WOK : forallb drv_win_ok (ss_mem (sQ c0 k)) = true) by (subst c0; unfold sQ; destruct (config_len data =? 0); [exact (proj1 sQ_win_ok) | exact (proj2 sQ_win_ok k)]).
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. destruct c0; destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem sPE0)); [exact HMB | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem sPE0)); [exact HMB | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem (sPE1 k))); [exact HMB | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem (sPE1 k))); [exact HMB | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia]. }
change (run_shape (payload data) (calls data) (in_fs inp)) with (loop_tgt (payload data) (calls data) 0%nat (calls data) (in_fs inp)).
apply (LOOPL sp inp xw xd E4 W ms1 (with_vm_backing (m_vm_lazy md) mat1 md) ly S a0 p data pb PNull cap 0 0%nat (calls data) (in_fs inp) Hargv Hsp Hva Hve Hvfs Hlk
ltac:(unfold dlen; lia)).
- intros j Hj. rewrite E4old by (unfold K_L, K_M1 in *; lia). subst E3. rewrite E_P_old by (unfold K_M1 in Hj; lia). cbn [ew edset]. apply ew_havoc_old. exact Hj.
- change (ed E4 2) with (ed E3 2). exact Ed2.
- rewrite E4old by (unfold K_L, A_BUF; lia). exact E41.
- rewrite E4old by (unfold K_L, A_LEN; lia). exact E42.
- rewrite E4old by (unfold K_L; lia). exact E60.
- rewrite V61. reflexivity.
- rewrite V62, (proj2 (Z.eqb_eq _ _) Hpl0). reflexivity.
- exact V63.
- rewrite V65. subst k. reflexivity.
- exact HSL.
- lia.
- lia.
- left. split; [exact Hpl0|]. split; [reflexivity | exact Hbl].
-   intros Hp. exfalso. lia.
- exact (drv_minv_frames _ _ _ Hminv).
- exact (drv_minv_qtight _ _ _ Hminv).
- exact HAI1.
- apply (AR_after_run B HB ARL ly S W E3 _ (ms_mem ms) (ms_mem ms1) md mat1 HAR WOK); [rewrite E3_0; exact Ulo | rewrite E3_0; exact HCT | exact HF1 |].
rewrite E3_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin a Ha)).
- exact HTOP.
- unfold EV_LIB, EV_MAX. lia.
- exact Hcap.
- unfold dlen. lia.
- left. split; [reflexivity | exact HIMG].
- exact HRO.
-   exact (finv_run B ly S W (ms_mem ms) md (w_H W) E3 _ _ _ usp HAR HFr1 WOK E3_0 Ulo Uhi HTOP HFI).
-   split; [intros k0; rewrite wvb_fds', Hfds; reflexivity|]. split; [rewrite wvb_fds', Hfds; reflexivity|].
split; [rewrite wvb_fs'; exact Hfs | exact (proj1 Hvfs)].
Qed.
Lemma pm_run : forall (c0 : bool) k E (W : world tfibsegs) ms md,
st_ok tfibsegs E (add_cond (sQ c0 k) cond_PL1) (restrict (w_H W) ms) ->
SRr tfibsegs W (mkCfg ms md) (at_st (sQ c0 k) (if c0 then sPM0 else sPM1 k) E W (ms_mem ms) md).
Proof.
intros c0 k E W ms md HS. pose proof HWXi as HWX. pose proof sPM_eq as [Q0 Q1].
destruct c0; unfold sQ in *; [rewrite <- Q0 | rewrite <- (Q1 k)]; unfold sPM, sQ; srr_run_with tfibtbl_lp_ok HS;
apply SRr_ret; (split; [reflexivity|]);
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => exists msx end; eexists; (split; [reflexivity|]);
(split; [exact HS|]); split; first [exact HF | exact HFr].
Qed.
Theorem tfib_run_Q_at : forall ws (W : world tfibsegs) ms md ly S data (pb : sptr) cap,
fs_lookup (in_fs inp) p = Some data -> 6 + config_len data <= dlen data ->
let E3 := E_P (edset (havoc EL K_M1 ws) 2 data) data (sptr_addr B ly pb + 2 + config_len data) in
tail_at B (sQ (config_len data =? 0) (Z.of_nat (calls data))) E3 sp inp a0 p data W ms md ly S pb cap ->
bv_unsigned (ew E3 K_PP) = sptr_addr B ly pb + 2 + config_len data ->
srealizes tfibsegs (mkCfg ms md) (run_shape (payload data) (calls data) (in_fs inp)).
Proof.
intros ws W ms md ly S data pb cap Hlk Hok E3 HT E60.
destruct (Z.eqb_spec (payload_len data) 0) as [Hpl0 | Hpl1]; [exact (tfib_run_Q_empty ws W ms md ly S data pb cap Hlk Hok Hpl0 HT E60)|].
destruct HT as (HS & E41 & E42 & HR & HAI & HAR & HTOP & Hbl & Hnev & Hcap & HLc & HBLK & Hfs & Hfds & Hminv & HFI).
pose proof Hsp as (Ulo & Uhi & U16). pose proof (u64_range sp) as Usp.
pose proof (top_ok_ceil _ _ HTOP) as HCT. pose proof (YM05.ceil_le_top _ HCT) as CLE. unfold stack_max_size in CLE.
set (buf := sptr_addr B ly pb) in *. set (c0 := config_len data =? 0) in *. set (k := Z.of_nat (calls data)) in *.
pose proof (config_len_bound data) as Hcl. unfold dlen in *.
assert (Hin : In (buf, cap) (ablocks B ly S)) by (unfold ablocks; rewrite Hbl; left; reflexivity).
pose proof (al_blocks _ _ ARL ly S W (ms_mem ms) md _ _ HAR Hin) as (_ & Hb4096 & Hbce & _).
assert (Hcap' : cap <= req_size cap) by (unfold req_size; destruct (Z.eqb_spec cap 0); lia).
assert (NIMG : forall a, buf <= a < buf + cap -> ~ in_img tfibsegs a).
{ intros a Ha. assert (Ha' : buf <= a < buf + req_size cap) by lia.
exact (proj2 (al_client_img _ _ ARL ly S W (ms_mem ms) md a HAR (or_introl (ex_intro _ _ (ex_intro _ cap (conj Hin Ha')))))). }
assert (E3_0 : bv_unsigned (ew E3 0) = usp) by (subst E3; rewrite E_P_old by lia; cbn [ew edset]; rewrite ew_havoc_old by (unfold K_M1; lia); reflexivity).
assert (Ed2 : ed E3 2 = data) by (subst E3; rewrite E_P_ed by lia; reflexivity).
destruct (list_len3 data ltac:(lia)) as (d0 & d1 & d2 & rest & Ed).
assert (UPL : U E3 sv_pl00 = payload_len data).
{ apply (U_pl00 E3 data d0 d1 (d2 :: rest) Ed2 Ed); unfold dlen; [exact E42 | lia | lia]. }
assert (Hplpos : 0 < payload_len data) by (unfold payload_len, dlen, HDR_MIN in *; lia).
assert (HS1 : st_ok tfibsegs E3 (add_cond (sQ c0 k) cond_PL1) (restrict (w_H W) ms)).
{ apply (st_ok_add_cond tfibsegs E3 (sQ c0 k) _ BC_NE sv_pl00 (SLit 0) HS). rewrite branch_ne_U, UPL, U_SLit. change (zcanon 0) with 0.
apply Bool.negb_true_iff. apply Z.eqb_neq. lia. }
apply (SRr_srealizes tfibsegs W (mkCfg ms md) _ _ (pm_run c0 k E3 W ms md HS1) HAI).
intros W0 c' _ HAI1 (-> & ms1 & mat1 & -> & HS2 & HF1 & HFr1). cbn [cfg_model] in HAI1.
pose proof (st_ok_mem_ok tfibsegs E3 _ _ HS2) as HM2. cbn [restrict ms_mem] in HM2.
assert (WOK : forallb drv_win_ok (ss_mem (sQ c0 k)) = true) by (subst c0; unfold sQ; destruct (config_len data =? 0); [exact (proj1 sQ_win_ok) | exact (proj2 sQ_win_ok k)]).
assert (Hwin : forall a, usp - 65536 <= a < usp -> apresent (w_H W) (ms_mem ms1) a).
{ intros a Ha. destruct c0; destruct (Z.lt_ge_cases a (usp - 128)).
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem sPM0)); [exact HM2 | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem sPM0)); [exact HM2 | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem (sPM1 k))); [exact HM2 | left; reflexivity | exact E3_0 | lia | lia | cbn; lia].
- eapply (win_present sp Hsp E3 (w_H W) (ms_mem ms1) (ss_mem (sPM1 k))); [exact HM2 | right; left; reflexivity | exact E3_0 | lia | lia | cbn; lia]. }
apply (RUNQM sp inp xw xd ws W ms1 _ ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk ltac:(unfold dlen; lia) Hplpos); [| exact E60].
fold buf E3. change (if config_len data =? 0 then sPM0 else sPM1 (Z.of_nat (calls data))) with (if c0 then sPM0 else sPM1 k).
split; [exact HS2|]. split; [exact E41|]. split; [exact E42|]. split.
{ eapply (runs_at_frame E3 (ss_facts (if c0 then sPM0 else sPM1 k)) (ss_mem (sQ c0 k)));
[exact (st_ok_facts_ok tfibsegs E3 _ _ HS2) | | exact HFr1 | rewrite E3_0; lia | exact HR].
subst c0. unfold sQ. pose proof wbs_PM as [WQ0 WQ1]. destruct (config_len data =? 0); [exact WQ0 | exact (WQ1 k)]. }
split; [exact HAI1|]. split.
{ apply (AR_after_run B HB ARL ly S W E3 _ (ms_mem ms) (ms_mem ms1) md mat1 HAR WOK); [rewrite E3_0; exact Ulo | rewrite E3_0; exact HCT | exact HF1 |].
rewrite E3_0. intros a Ha. exact (apresent_some' _ _ _ (Hwin a Ha)). }
split; [exact HTOP|]. split; [exact Hbl|]. split; [exact Hnev|]. split; [exact Hcap|]. split; [unfold dlen; lia|]. split.
{ unfold dlen. apply (blk_of_frame_r _ _ _ _ _ buf (Z.of_nat (length data)) data usp HFr1 WOK E3_0 Ulo); [intros a Ha; apply NIMG; lia | lia | lia | exact HBLK]. }
split; [rewrite wvb_fs'; exact Hfs |]. split; [rewrite wvb_fds'; exact Hfds |]. split; [exact Hminv|].
exact (finv_run B ly S W (ms_mem ms) md (w_H W) E3 _ _ _ usp HAR HFr1 WOK E3_0 Ulo Uhi HTOP HFI).
Qed.
End g.
Theorem tfib_run_Q (B : asyms) (HB : TfibSyms B) (ARL : AR_laws tfibsegs B) (xst : nat -> (word -> bool) -> (word -> option byte) -> Prop)
(LOOPL : loop_L_x B xst) (RUNQM : run_QM_tfa B) : run_Q_tfa B.
Proof.
intros sp inp xw xd ws W ms md ly S a0 p data pb cap Hargv Hsp Hva Hve Hvfs Hlk Hok E3 HT E60.
exact (tfib_run_Q_at B HB ARL xst LOOPL RUNQM sp inp xw xd a0 p Hargv Hsp Hva Hve Hvfs ws W ms md ly S data pb cap Hlk Hok HT E60).
Qed.
End e.
