(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: new file holding text copied from A/AD2d.v:31-33, 158-240 with renamed
   definitions, and the first-call facts of fuzz_reply's program globals: the call-site entry of target_run's loop onto
   A/AD2f_fp.v's clipped view (refines_BF, pe_to_LF: the donor's refines_B / pe_to_L with L_memF / S_LF), and, for the
   cf driver's first call (A/AD1w_cf.v fr_lib_inv_init), what the call-site state gives about each byte of the 20
   program objects G_fr_obj (GF_OBJ): its view is its image byte (sPE_gf_img: every object lies in a CImg chunk of
   IMG_E, gf_cover_chk) and it is writable (sPE_gf_writable: every object lies in the writable window of an absolute
   region of IMG_E, gf_win_chk), so it holds gf_init a, the image byte (gf_init_rom).  Form of
   omx-clap-core/fuzz_state's clip_ivs_ok / clipL_ok / pstat_cover_chk / sPE_pstat_img (a working branch
   b7573d0eb37).  Presence (apresent) is NOT given: LPS starts ms_mem with the stack only (Run.v init_machine_state),
   and start-up never stores to these objects. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO0d YO0f.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YK00 YK0h YK14 YK1b YK15 YK18 YK0p YP0n YK0s YM02 YP0m YP09 YP02 YP0l YP0k YP06 YP08 YP03 YP0g YP0e YN3q YN3v YI04 YL0a YL09 YL02 YL04 YK04 YA0i YA0n YA0o YA0p YA0m YK09 YA0e YG00 YG01 YG0f YG0v YG0n YG0d YCe5.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v AB12 AF0l AB1h AB13 AF0m AD2j AD2i AD1t AD20 AD1v AD1y AD26 AD24.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACeg.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD21 AD25 AD23 AD2h AD1w AD2f AD2b AD2g AD1s AD2c AD2d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO05 YO09 YO06 YO01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AD2f_fp.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

(* ---- the clip refines (fpgen AD2d.v pieces_ok_single / clip_ivs_ok / clipL_ok) ---- *)
Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma pieces_ok_single : forall E m r, r_lo r <= r_hi r -> pieces_ok E m r [r].
Proof.
intros E m r Hr. split; [intros H; constructor; [exact H | constructor] |]. split; [constructor; [apply ext_in_refl | constructor] |].
split; [cbn; split; exact I |]. constructor; [exact Hr | constructor].
Qed.
Lemma clip_ivs_ok : forall E m ivs r, r_lo r <= r_hi r -> Forall (fun iv => fst iv <= snd iv) ivs -> pieces_ok E m r (clip_ivs ivs r).
Proof.
intros E m ivs r Hr Hiv. unfold clip_ivs. induction ivs as [|iv ivs IH]; cbn [fold_right].
- apply pieces_ok_single. exact Hr.
- apply flat_map_pieces_ok; [apply IH; exact (Forall_inv_tail Hiv) |].
intros q _ Hq. apply clip_out_ok; [exact (Forall_inv Hiv) | exact Hq].
Qed.
Lemma GF_IVS_le : Forall (fun iv => fst iv <= snd iv) GF_IVS.
Proof. unfold GF_IVS, GF_RANGES. cbn [map]. repeat (constructor; [cbn; lia |]). constructor. Qed.
Lemma clipLF_ok : forall E m r, r_lo r <= r_hi r -> pieces_ok E m r (clipLF r).
Proof.
intros E m r Hlh. unfold clipLF.
apply flat_map_pieces_ok; [| intros q _ Hq; apply clip_ivs_ok; [exact Hq | exact GF_IVS_le]].
apply flat_map_pieces_ok; [apply clip_out_ok; [unfold STDOUT_LO, STDOUT_HI; lia | exact Hlh] |].
intros q _ Hq. apply clip_out_ok; [unfold SOBUF_LO, SOBUF_HI; lia | exact Hq].
Qed.
End e.

(* ---- the call-site entry onto the clipped view (AD2d.v:31-33, 158-240) ---- *)
Lemma L_piecesF_unfold : L_piecesCF = [ [WIN208; TRFc] ] ++ map (fun r => [r]) (firstn 2 (skipn 1 (ss_mem S_Pm)))
++ map clipLF IMG_E ++ map (fun _ => @nil YP09.region) B1_r5.
Proof. vm_compute. reflexivity. Qed.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {LS : lib_shape}.
Lemma refines_BF : forall (c0 : bool) k E3 (m : word -> option byte),
refines E3 m (ss_mem (if c0 then sPE0 else sPE1 k)) L_piecesCF.
Proof.
intros c0 k E3 m. rewrite L_piecesF_unfold.
assert (IMG : refines E3 m IMG_E (map clipLF IMG_E)).
{ apply refines_map. intros r Hr. pose proof (proj1 (forallb_forall _ _) IMG_E_lohi r Hr) as Hlh. cbn beta in Hlh. apply Z.leb_le in Hlh.
apply clipLF_ok. exact Hlh. }
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
Lemma pe_to_LF : forall (c0 : bool) (k : Z) E3 (W : world tfibsegs) ms (n : Z),
st_ok tfibsegs E3 (if c0 then sPE0 else sPE1 k) (restrict (w_H W) ms) ->
U E3 sv_pl00 = n -> 0 <= n <= 2 ^ 26 -> 1 <= k <= 4 -> (c0 = true -> k = 1) ->
let E' := E_L E3 (ms_regs ms) in
st_ok tfibsegs E' S_LF (restrict (w_H W) ms)
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
assert (HM1 : mem_ok tfibsegs E3 (mrestrict (w_H W) (ms_mem ms)) L_memF).
{ rewrite <- (proj2 L_piecesCF_eq). apply (mem_ok_refine E3 _ (ss_mem (if c0 then sPE0 else sPE1 k))).
- subst ss. exact HM0.
- apply refines_BF.
- rewrite (proj2 L_piecesCF_eq). exact (proj1 L_memF_wf). }
assert (HM2 : mem_ok tfibsegs E' (mrestrict (w_H W) (ms_mem ms)) L_memF).
{ apply (mem_ok_agree tfibsegs K_L E3); [| exact (proj1 (proj2 L_memF_wf)) | exact HM1].
split; [| subst E'; reflexivity]. intros j Hj. subst E'. unfold E_L. rewrite ew_havoc_old by exact Hj. reflexivity. }
pose proof sPE_mem as (_ & _ & P0 & P1 & _).
assert (Hpc : ss_pc ss = A_LLVMF) by (subst ss; destruct c0; [exact P0 | exact (P1 k)]).
unfold S_LF. rewrite <- Hpc.
apply (st_ok_reabs tfibsegs LT162 E3 E' ss (restrict (w_H W) ms) L_regs L_memF L_facts HS).
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
End f.

(* ---- the program objects at the first call ---- *)
(* the 20 program objects (W_LLVMFuzzerTestOneInput_G.v G_fr_obj; A/AD1r_fp.v proves G_fr_obj = GF_OBJ) *)
Definition GF_OBJ : list (Z * Z) := removelast GF_RANGES.
Lemma GF_OBJ_val : GF_OBJ =
  [ (0x5d88e0, 384); (0x5d8820, 4); (0x5d8b40, 8); (0x5d88c0, 8); (0x5d8b20, 8); (0x5d8840, 8);
    (0x5d88a0, 1); (0x5d8880, 1); (0x5d8860, 1); (0x5d8ac0, 40); (0x5d8740, 8); (0x5d8760, 1);
    (0x5d8780, 4); (0xa1fc0, 4); (0xa1fe0, 4); (0x5d87e0, 1); (0xa1fa0, 8); (0x5d87c0, 8);
    (0x5d87a0, 4); (0x5d8800, 4) ].
Proof. reflexivity. Qed.
(* every object lies in CImg cells of IMG_E, and in the writable window of an absolute region of IMG_E *)
Lemma gf_cover_chk : forallb (fun g => cover_from 200 IMG_CELLS (fst g) (fst g + snd g)) GF_OBJ = true.
Proof. vm_compute. reflexivity. Qed.
Definition gf_win_ok (g : Z * Z) : bool :=
  existsb (fun r => match r_base r with None => ((r_wlo r <=? fst g) && (fst g + snd g <=? r_whi r))%bool | Some _ => false end) IMG_E.
Lemma gf_win_chk : forallb gf_win_ok GF_OBJ = true.
Proof. vm_compute. reflexivity. Qed.
Lemma sPE_IMG_E_in : forall (c0 : bool) k r, In r IMG_E -> In r (ss_mem (if c0 then sPE0 else sPE1 k)).
Proof. intros c0 k r Hr. destruct c0; [rewrite sPE0_split | rewrite sPE1_split]; right; apply in_app_iff; right; apply in_app_iff; left; exact Hr. Qed.
(* for any symbolic memory M holding IMG_E's regions (the call site sPE0 / sPE1 here, the payload call site S_PL0 /
   S_PL1 in A/AD2e_fp.v) *)
Lemma img_gf_view : forall M E (H : word -> bool) m,
  mem_ok tfibsegs E (mrestrict H m) M -> (forall r, In r IMG_E -> In r M) ->
  forall a, Exists (in_zr a) GF_OBJ -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof.
intros M E H m HM HIn a Ha. apply Exists_exists in Ha as (g & Hg & Hz). unfold in_zr in Hz.
pose proof (proj1 (forallb_forall _ _) gf_cover_chk g Hg) as Hc.
destruct (cover_from_sound _ _ _ _ Hc a ltac:(lia)) as ([clo cl] & Hin & Hca). cbn [fst snd] in Hca.
exact (img_cells_view IMG_E E H m _ clo cl IMG_CELLS_eqE HM HIn Hin a Hca).
Qed.
Lemma img_gf_writable : forall M E (H : word -> bool) m,
  mem_ok tfibsegs E (mrestrict H m) M -> (forall r, In r IMG_E -> In r M) ->
  forall a, Exists (in_zr a) GF_OBJ -> writable_at tfibsegs (mrestrict H m) a.
Proof.
intros M E H m (_ & Hok & _) HIn a Ha. apply Exists_exists in Ha as (g & Hg & Hz). unfold in_zr in Hz.
pose proof (proj1 (forallb_forall _ _) gf_win_chk g Hg) as Hw. unfold gf_win_ok in Hw.
apply existsb_exists in Hw as (r & Hr & Hrw).
destruct (r_base r) as [n|] eqn:Eb; [discriminate Hrw|]. apply andb_prop in Hrw as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
pose proof (proj1 (Forall_forall _ _) Hok r (HIn r Hr)) as (_ & _ & RW & _).
rewrite Eb in RW. cbn [base_val] in RW. specialize (RW a ltac:(lia)). rewrite Z.add_0_l in RW. exact RW.
Qed.
Lemma sPE_gf_img : forall (c0 : bool) k E (H : word -> bool) m,
  mem_ok tfibsegs E (mrestrict H m) (ss_mem (if c0 then sPE0 else sPE1 k)) ->
  forall a, Exists (in_zr a) GF_OBJ -> aview tfibsegs H m a = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)).
Proof. intros c0 k E H m HM. exact (img_gf_view _ E H m HM (sPE_IMG_E_in c0 k)). Qed.
Lemma sPE_gf_writable : forall (c0 : bool) k E (H : word -> bool) m,
  mem_ok tfibsegs E (mrestrict H m) (ss_mem (if c0 then sPE0 else sPE1 k)) ->
  forall a, Exists (in_zr a) GF_OBJ -> writable_at tfibsegs (mrestrict H m) a.
Proof. intros c0 k E H m HM. exact (img_gf_writable _ E H m HM (sPE_IMG_E_in c0 k)). Qed.
(* the start-up value of an object byte: its image byte (0 where the image has none) *)
Definition gf_init (a : Z) : Z :=
  match seg_rom tfibsegs (Z_to_bv 64 a) with Some b => bv_unsigned b | None => 0 end.
Lemma gf_init_rom : forall a,
  Some (gf_init a) = option_map (fun b : byte => bv_unsigned b) (seg_rom tfibsegs (Z_to_bv 64 a)) \/
  (seg_rom tfibsegs (Z_to_bv 64 a) = None /\ gf_init a = 0).
Proof. intros a. unfold gf_init. destruct (seg_rom tfibsegs (Z_to_bv 64 a)); [left | right]; auto. Qed.
Lemma gf_rom_some : forall a, Exists (in_zr a) GF_OBJ -> seg_rom tfibsegs (Z_to_bv 64 a) <> None.
Proof.
intros a Ha. apply Exists_exists in Ha as (g & Hg & Hz). rewrite GF_OBJ_val in Hg. unfold in_zr in Hz.
apply tfib_rom_all. repeat (destruct Hg as [<-|Hg]; [cbn [fst snd] in Hz; lia|]). destruct Hg.
Qed.
(* at a call site, every object byte reads gf_init and is writable *)
Lemma img_gf_start : forall M E (W : world tfibsegs) mem,
  mem_ok tfibsegs E (mrestrict (w_H W) mem) M -> (forall r, In r IMG_E -> In r M) ->
  forall a, Exists (in_zr a) GF_OBJ ->
  aview tfibsegs (w_H W) mem a = Some (gf_init a) /\ writable_at tfibsegs (mrestrict (w_H W) mem) a.
Proof.
intros M E W mem HM HIn a Ha. split; [| exact (img_gf_writable M E (w_H W) mem HM HIn a Ha)].
rewrite (img_gf_view M E (w_H W) mem HM HIn a Ha). unfold gf_init.
destruct (seg_rom tfibsegs (Z_to_bv 64 a)) eqn:Er; [reflexivity|]. exfalso. exact (gf_rom_some a Ha Er).
Qed.
Lemma sPE_gf_start : forall (c0 : bool) k E (W : world tfibsegs) mem,
  mem_ok tfibsegs E (mrestrict (w_H W) mem) (ss_mem (if c0 then sPE0 else sPE1 k)) ->
  forall a, Exists (in_zr a) GF_OBJ ->
  aview tfibsegs (w_H W) mem a = Some (gf_init a) /\ writable_at tfibsegs (mrestrict (w_H W) mem) a.
Proof. intros c0 k E W mem HM. exact (img_gf_start _ E W mem HM (sPE_IMG_E_in c0 k)). Qed.
