(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMsnprintfPcA.v at a working branch 5d8d8a15571, relocated A->B by Theorem Labs tools over the unstripped twins; every image numeral re-derived by symbol / section (a Theorem Labs lane reloc report). *)
(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: canary_val follows A/AE36.v rdword_img_some / img_aview_some for musl's
   stack-protector guard; pc_ro_ok follows A/AE3i.v region_ok_img_of over img_ro_chunks, from rom_viewN; the symbolic
   states and the other lemmas are new. *)
(* musl printf_core (fm.asan 0x8f278) for fm's snprintf formats: the symbolic states the walks start from and the facts
   about memory views they share. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import FMsnprintfPc0.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---- the symbolic states: frame base (atom 2) = sp0, vfprintf's entry sp; atom 32 = P (the arg slots, the value of
   ap2), atom 33 = the stack-protector guard's value, atoms 34.. = the slots' values ---- *)
Definition pc_stk : YP09.region :=
  YP09.mkRegion (Some 2%nat) (- SNK_STK) 0 (- SNK_STK) (OSP_PC + 8) [YP09.mkChunk OSP_PC (CVal 8 (SOff 32 0))].
Definition pc_stk0 : YP09.region := YP09.mkRegion (Some 2%nat) (- SNK_STK) 0 (- SNK_STK) OSP_PC [].
Definition pc_flg : YP09.region := YP09.mkRegion (Some 2%nat) FO (FO + 4) FO FO [YP09.mkChunk FO (CVal 4 (SLit 0))].
Definition pc_gotc : YP09.region :=
  YP09.mkRegion None FM_GOT_canary (FM_GOT_canary + 8) 0 0 [YP09.mkChunk FM_GOT_canary (CVal 8 (SLit FM_canary))].
Definition pc_can : YP09.region := YP09.mkRegion None FM_canary (FM_canary + 8) 0 0 [YP09.mkChunk FM_canary (CVal 8 (SOff 33 0))].
(* the read-only image minus fm's runtime-owned static pieces (AE3i img_ro_chunks): what rom_viewN pins *)
Definition pc_ro : YP09.region := img_ro_region.
Fixpoint slot_chunks (i n : nat) : list YP09.chunk :=
  match n with O => [] | S n' => YP09.mkChunk (8 * Z.of_nat i) (CVal 8 (SOff (34 + i) 0)) :: slot_chunks (S i) n' end.
Definition pc_slots (n : nat) : YP09.region := YP09.mkRegion (Some 32%nat) 0 (8 * Z.of_nat n) 0 0 (slot_chunks 0 n).
(* the regions after the stack region once the GOT cell is read (printf_core reads it only in its prologue) *)
Definition pc_rest (n : nat) : smem := [pc_flg; pc_can; pc_slots n; pc_ro].
Definition pc_regs (f fv : Z) : list sv :=
  sr_set (sr_set (sr_set (sr_set (sr_set (sr_set sr_atoms (2%bv : bv 5) (SOff 2 OSP_PC))
    (10%bv : bv 5) (if f =? 0 then SLit 0 else SOff 2 FO)) (11%bv : bv 5) (SLit fv)) (12%bv : bv 5) (SOff 2 OSP_PC))
    (13%bv : bv 5) (SOff 2 (OSP_PC + 0x60))) (14%bv : bv 5) (SOff 2 (OSP_PC + 0x108)).
Definition pc_facts_s : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (32%nat, mkAF (2 ^ 44) (2 ^ 47) 0); (34%nat, mkAF 4096 (2 ^ 47) 0) ] [] [].
Definition pc_facts_p : facts :=
  mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4); (32%nat, mkAF (2 ^ 44) (2 ^ 47) 0); (34%nat, mkAF 1 (2 ^ 30) 0);
    (35%nat, mkAF 4096 (2 ^ 47) 0); (36%nat, mkAF 4096 (2 ^ 47) 0) ] [] [].
Definition pc_facts0 : facts := mkFacts [ (2%nat, mkAF (2 ^ 44) (2 ^ 47) 4) ] [] [].
(* second pass (f = the FILE) and first pass (f = 0) *)
Definition pc_s0 (fv : Z) (n : nat) : sstate :=
  mkSS A_PCORE (pc_regs 1 fv) (pc_stk :: pc_rest n ++ [pc_gotc]) None (if (n =? 1)%nat then pc_facts_s else pc_facts_p).
Definition pc_t0 (fv : Z) : sstate := mkSS A_PCORE (pc_regs 0 fv) [pc_stk0; pc_gotc; pc_can; pc_ro] None pc_facts0.
Definition PRUN (s : sstate) : sstate * run_status := sym_run_toN tfibsegs tfibmusl_tbl FUEL A_FWX s.
(* the return address a call leaves in ra, and a stop at a branch *)
Definition RAof (s : sstate) : Z := match sr_get (ss_regs s) 1%bv with SLit z => z | _ => 0 end.
Definition br_c (st : run_status) : branch_cond := match st with RS_stopped (SR_branch c _ _) => c | _ => BC_EQ end.
Definition br_a (st : run_status) : sv := match st with RS_stopped (SR_branch _ a _) => a | _ => SLit 0 end.
Definition br_b (st : run_status) : sv := match st with RS_stopped (SR_branch _ _ b) => b | _ => SLit 0 end.
(* drop the GOT cell's region (the last) *)
Definition pc_drop (s : sstate) : sstate := mkSST (ss_pc s) (ss_regs s) (ss_fregs s) (removelast (ss_mem s)) (ss_resv s) (ss_facts s).

(* ---- memory views ---- *)
Lemma seg0_info : map (fun sg => (seg_base sg, seg_size sg, seg_writable sg)) tfibsegs =
  [(65536%N, 131072%N, false); (196608%N, 430080%N, false); (626688%N, 8192%N, true); (634880%N, 5619712%N, true)].
Proof. vm_compute. reflexivity. Qed.
Lemma in_rom_seg0 : forall a, 0x10000 <= a < 0x30000 -> in_rom tfibsegs a.
Proof.
intros a Ha. pose proof seg0_info as Hm.
destruct tfibsegs as [|sg rest] eqn:Es; [discriminate Hm|]. cbn [map] in Hm. injection Hm as Hb Hs Hw _.
exists sg. split; [left; reflexivity|]. split; [exact Hw|]. rewrite Hb, Hs. cbn. lia.
Qed.
Lemma bv8_unsigned_inj : forall b b' : byte, bv_unsigned b = bv_unsigned b' -> b = b'.
Proof. intros b b' H. apply bv_eq. exact H. Qed.
(* no byte of the walks' read-only region is an owned static or errno *)
Definition ro_freeb (c : YP09.chunk) : bool :=
  forallb (fun r => (YP09.c_off c + c_len c <=? fst r) || (fst r + snd r <=? YP09.c_off c)) Tfib_owned_static &&
  (YP09.c_off c + c_len c <=? TFIB_ERRNO).
Lemma ro_chunks_free : forallb ro_freeb img_ro_chunks = true.
Proof. vm_compute. reflexivity. Qed.
(* rom_viewN pins every read-only image byte that is neither an owned static nor errno, so the region holds *)
Lemma pc_ro_ok : forall (B : asyms) E (W : world tfibsegs) mem, TfibSyms B -> rom_viewN tfibsegs B W mem ->
  region_ok tfibsegs E (mrestrict (w_H W) mem) pc_ro.
Proof.
intros B E W mem TB Hrv. unfold region_ok, pc_ro, img_ro_region.
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
split; [unfold IMG_RO_LO; lia|]. split; [unfold IMG_RO_HI; lia|]. split; [intros o Ho; lia|].
apply Forall_forall. intros c Hc i Hi.
pose proof (proj1 (Forall_forall _ _) img_ro_chunks_inside c Hc) as (Hlo & Hhi & n & Hv).
pose proof (proj1 (forallb_forall _ _) img_ro_bytes_ok c Hc) as Hz. cbn beta in Hz.
pose proof (zallb_sound _ _ _ (YP09.c_off c + i) Hz ltac:(lia)) as Hb.
pose proof (proj1 (forallb_forall _ _) ro_chunks_free c Hc) as Hf. unfold ro_freeb in Hf.
apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf2.
rewrite !Z.add_0_l. destruct c as [co cv]; cbn [YP09.c_off YP09.c_val] in *. subst cv.
cbn [c_len cv_len] in Hi, Hhi, Hf2. cbn [cbyte].
assert (Hno : ~ Exists (in_zr (co + i)) (as_owned_static B)).
{ rewrite (ts_owned B TB). intros HE. apply Exists_exists in HE as (r & Hr & Hin).
  pose proof (proj1 (forallb_forall _ _) Hf1 r Hr) as Hrr. cbn beta in Hrr. cbn [YP09.c_off c_len cv_len] in Hrr.
  unfold in_zr in Hin. apply orb_prop in Hrr as [Hrr|Hrr]; apply Z.leb_le in Hrr; lia. }
assert (Her : ~ (as_errno B <= co + i < as_errno B + 4)) by (rewrite (ts_errno B TB); lia).
pose proof (Hrv (co + i) (in_rom_seg0 (co + i) ltac:(unfold IMG_RO_LO, IMG_RO_HI in *; lia)) Hno Her) as Hv'.
unfold img_byte_ok, img_byte in Hb. destruct (seg_rom tfibsegs (Z_to_bv 64 (co + i))) as [b|] eqn:Eb; [|discriminate].
exists b. split; [unfold img_byte; rewrite Eb; reflexivity|].
unfold aview in Hv'. destruct (mbyte tfibsegs (mrestrict (w_H W) mem) (co + i)) as [b'|] eqn:Eb'; [|discriminate].
cbn [option_map] in Hv'. injection Hv' as Hv'. rewrite (bv8_unsigned_inj _ _ Hv'). reflexivity.
Qed.
(* musl's word constants (mconsts_view) are non-owned read-only bytes *)
Lemma mc_freeb : forallb (fun r => (MC_HI <=? fst r) || (fst r + snd r <=? MC_LO)) Tfib_owned_static && (MC_HI <=? TFIB_ERRNO) = true.
Proof. vm_compute. reflexivity. Qed.
Lemma mconsts_of_rom_viewN : forall (B : asyms) (W : world tfibsegs) mem, TfibSyms B -> rom_viewN tfibsegs B W mem -> mconsts_view W mem.
Proof.
intros B W mem TB Hrv a Ha. pose proof mc_freeb as Hf. apply andb_prop in Hf as [Hf1 Hf2]. apply Z.leb_le in Hf2.
pose proof mc_bounds as (E1 & E2). apply Hrv.
- apply in_rom_seg0. lia.
- rewrite (ts_owned B TB). intros HE. apply Exists_exists in HE as (r & Hr & Hin).
  pose proof (proj1 (forallb_forall _ _) Hf1 r Hr) as Hrr. cbn beta in Hrr. unfold in_zr in Hin.
  apply orb_prop in Hrr as [Hrr|Hrr]; apply Z.leb_le in Hrr; lia.
- rewrite (ts_errno B TB). lia.
Qed.
(* a visible byte stays visible when every present byte stays present *)
Lemma aview_some_mono : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall a, apresent H m a -> apresent H m' a) -> aview tfibsegs H m a <> None -> aview tfibsegs H m' a <> None.
Proof.
intros H m m' a Hp Hv. unfold aview, mbyte, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:Eh.
- exact Hv.
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp a ltac:(split; [exact Eh | exists b; exact Em])) as [_ [b' Hb']]. rewrite Hb'. cbn. discriminate.
  + destruct (m' (Z_to_bv 64 a)); [cbn; discriminate | exact Hv].
Qed.
Lemma writable_mono : forall (H : word -> bool) (m m' : word -> option byte) a,
  (forall a, apresent H m a -> apresent H m' a) -> writable_at tfibsegs (mrestrict H m) a -> writable_at tfibsegs (mrestrict H m') a.
Proof.
intros H m m' a Hp Hw. unfold writable_at, wview, mrestrict in *.
destruct (H (Z_to_bv 64 a)) eqn:Eh.
- exact Hw.
- destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
  + destruct (Hp a ltac:(split; [exact Eh | exists b; exact Em])) as [_ [b' Hb']]. rewrite Hb'. discriminate.
  + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
(* the guard's value exists in any memory (it is an image byte range) *)
Lemma canary_bytes_ok : zallb (img_byte_ok tfibsegs) FM_canary 8%nat = true.
Proof. vm_compute. reflexivity. Qed.
Lemma canary_val : forall (H : word -> bool) m, exists v, val_mem tfibsegs (mrestrict H m) FM_canary 8 v /\ 0 <= v < 2 ^ 64.
Proof.
intros H m.
assert (B : forall k, 0 <= k < 8 -> exists v, aview tfibsegs H m (FM_canary + k) = Some v /\ 0 <= v < 256).
{ intros k Hk. pose proof (zallb_sound _ _ _ (FM_canary + k) canary_bytes_ok ltac:(lia)) as Hi.
  unfold aview, mbyte. destruct (mrestrict H m (Z_to_bv 64 (FM_canary + k))) as [b|].
  - exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
  - unfold img_byte_ok, img_byte in Hi. destruct (seg_rom tfibsegs (Z_to_bv 64 (FM_canary + k))) as [b|]; [|discriminate].
    exists (bv_unsigned b). split; [reflexivity|]. pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia. }
destruct (B 0 ltac:(lia)) as (v0 & E0 & R0). destruct (B 1 ltac:(lia)) as (v1 & E1 & R1).
destruct (B 2 ltac:(lia)) as (v2 & E2 & R2). destruct (B 3 ltac:(lia)) as (v3 & E3 & R3).
destruct (B 4 ltac:(lia)) as (v4 & E4 & R4). destruct (B 5 ltac:(lia)) as (v5 & E5 & R5).
destruct (B 6 ltac:(lia)) as (v6 & E6 & R6). destruct (B 7 ltac:(lia)) as (v7 & E7 & R7).
rewrite Z.add_0_r in E0. eexists. split; [apply val_mem_of_rdword; unfold rdword; rewrite E0, E1, E2, E3, E4, E5, E6, E7; reflexivity|].
lia.
Qed.
End a.
