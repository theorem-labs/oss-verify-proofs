(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ARM_gone of the ASan walk of fuzz_reply's LLVMFuzzerTestOneInput, PHASE 2:
   the reads[] loop 0x84738-0x84834 (fuzz_reply.c:640-641 `reads[k] = g_s[k].open && relay_reads(&g_s[k])`), from
   the loop's head GL1 q to relay_instance_gone's call GRG.  The arm's base, its cut points and the texts of the
   model obligations are in lib/A/W_LLVMFuzzerTestOneInput_gone_base.v; this file proves its hypothesis GP2.
   The walk, by three restarts of the symbolic state (the engine resolves an address only as an atom plus a
   constant, so each block that indexes by k starts from a fresh atom):
     g2_pre   0x84738 -> 0x8474c   a1 = &g_s[k], a0 = &g_s[k].open (pure ALU, no memory)
     g2_body  0x8474c -> 0x847ec   the two instrumented checks of the slot, g_s[k].open, g_nsrc, g_src, and
                                   the INLINED relay_source search (g2_scan) - a0 is reads[k]
     g2_tail  0x847ec -> 0x84738 / 0x84834   the store of reads[k] and the latch
   Every instrumented check of this phase is decided inside the run: the slot's granules lie in the instance's
   zero-shadow ranges (GN_HZS, via azs_range_addressable), and the table entry's lie inside the table's
   896-byte block (range_addressable_of_block).  The partial-granule arms 0x84804 / 0x84814 / 0x847b8 / 0x84824,
   and with them the error path 0x84ebc, are therefore not reached. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB1v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AE2k.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import ACfn.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import ZTraceSpec.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_syms W_listing W_place W_tbl W_kit W_pl W_img W_journal.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import
HarnessRep RelayRep CheckRep RelayKeys RelayModel.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require RelayRunT drain_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_rep.
Import ListNotations.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import
W_LLVMFuzzerTestOneInput_cut W_contract W_sites W_frame W_rebase W_rep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_base.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import W_LLVMFuzzerTestOneInput_gone_tk.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
(* W_LLVMFuzzerTestOneInput_gone_tk.v turns the euclidean-division equations off for lia; this file's
   alignment goals (g_s mod 32, the table's entry mod 8) need them, so they are on again here. *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section gp2.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB : Z -> Z.
Variables RLO RHI : Z.
Variable fr_live_pre : astate -> Prop.
Variable G_fr : list (Z * Z).
Variable fr_FP : bvmap 5 word -> alayout -> astate -> world segs -> (word -> option byte) -> list (Z * Z).
Hypothesis LAWS : AR_laws segs B.
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.
(* g_s lies in the instance's zero-shadow ranges: the base's model obligation, verbatim *)
Hypothesis HZS : GN_HZS B.
(* errno's place: the base's model obligation, verbatim (the transport of amodel_at across the store) *)
Hypothesis HERRNO : GN_ERRNO_LOW B.
#[local] Notation VAL := (@pa_val _ fr_prog_listing PB_fr).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PB_fr A_TEXT).

(* ------------------------------------------------------------------ the phase's own addresses *)
Definition AF_gn_sh1 : Z := 0x2460.   (* 0x8474c: the instrumented check of &g_s[k].open *)
Definition AF_gn_v : Z := 0x2500.     (* 0x847ec: a0 is reads[k]; the store and the latch follow *)
Definition AF_gn_sw : Z := 0x250c.    (* 0x847f8: sw a0,0(a1) *)

(* ------------------------------------------------------------------ gn_find, as the search walks it *)
Lemma g2_find_none_from : forall es fd i,
  (forall u, (u < length es)%nat -> re_fd (nth u es gn_e0) <> fd) -> gn_find es fd i = None.
Proof.
  induction es as [|e es IH]; intros fd i HN; [reflexivity|].
  cbn [gn_find]. destruct (Z.eqb_spec (re_fd e) fd) as [Heq|_].
  - exfalso. apply (HN 0%nat ltac:(cbn [length]; lia)). cbn [nth]. exact Heq.
  - apply IH. intros u Hu. apply (HN (S u)). cbn [length]. lia.
Qed.
Lemma g2_find_some_from : forall es fd i0 i,
  (i0 < length es)%nat -> re_fd (nth i0 es gn_e0) = fd ->
  (forall u, (u < i0)%nat -> re_fd (nth u es gn_e0) <> fd) ->
  gn_find es fd i = Some (i + i0)%nat.
Proof.
  induction es as [|e es IH]; intros fd i0 i Hi0 Heq HN; cbn [length] in Hi0; [lia|].
  cbn [gn_find]. destruct i0 as [|i0].
  - cbn [nth] in Heq. rewrite Heq, Z.eqb_refl. f_equal. lia.
  - destruct (Z.eqb_spec (re_fd e) fd) as [Hbad|_].
    + exfalso. apply (HN 0%nat ltac:(lia)). cbn [nth]. exact Hbad.
    + rewrite (IH fd i0 (S i) ltac:(lia) Heq ltac:(intros u Hu; apply (HN (S u)); lia)). f_equal. lia.
Qed.

(* ------------------------------------------------------------------ zero-shadow ranges, narrowed *)
Lemma g2_azs_sub : forall a n a' n', azs B a n -> a <= a' -> a' + n' <= a + n -> azs B a' n'.
Proof.
  intros a n a' n' (r & Hin & H8 & Hlo & Hhi) H1 H2.
  exists r. split; [exact Hin|]. split; [exact H8|]. split; lia.
Qed.

(* ------------------------------------------------------------------ the bytes of the relay's table.
   The 4-byte fd and eof fields of entry i, read out of atable_at.  (The shape of
   W_LLVMFuzzerTestOneInput_drain.v's dr_tbl_fd / W_xorder.v's lxo_tbl_fd, with the eof field added; copied
   here under this file's prefix so that the piece does not import another piece's file.) *)
Lemma g2_ent_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes.
  rewrite !length_app, !Mem.length_le4, !Mem.length_le8, H1, H2. reflexivity.
Qed.
Lemma g2_cc_len : forall es,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  length (concat (map entry_bytes es)) = (56 * length es)%nat.
Proof.
  induction es as [|e es IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat length]. rewrite length_app, g2_ent_len, IH by assumption. lia.
Qed.
Lemma g2_cc_nth : forall es i k d,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (i < length es)%nat -> (k < 56)%nat ->
  nth (56 * i + k) (concat (map entry_bytes es)) d = nth k (entry_bytes (nth i es gn_e0)) d.
Proof.
  induction es as [|e es IH]; intros i k d HF Hi Hk; cbn [length] in Hi; [lia|].
  apply Forall_cons_iff in HF as [[H1 H2] HF].
  cbn [map concat]. destruct i as [|i].
  - replace (56 * 0 + k)%nat with k by lia. cbn [nth].
    apply app_nth1. rewrite g2_ent_len by assumption. exact Hk.
  - rewrite app_nth2 by (rewrite g2_ent_len by assumption; lia).
    rewrite g2_ent_len by assumption.
    replace (56 * S i + k - 56)%nat with (56 * i + k)%nat by lia.
    cbn [nth]. apply IH; [exact HF | lia | exact Hk].
Qed.
Lemma g2_nth_le_bytes : forall n z k d, (k < n)%nat ->
  nth k (Z_to_le_bytes n z) d = Z_to_bv 8 (Z.shiftr z (8 * Z.of_nat k)).
Proof.
  induction n as [|n IH]; intros z k d Hk; [lia|].
  cbn [Z_to_le_bytes]. destruct k as [|k].
  - cbn [nth]. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r. reflexivity.
  - cbn [nth]. rewrite IH by lia. f_equal.
    rewrite Z.shiftr_shiftr by lia. f_equal. lia.
Qed.
Lemma g2_le4_byte : forall v k, 0 <= v < 2 ^ 32 -> (k < 4)%nat ->
  bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0)) = YO0f.le_byte v 4 k.
Proof.
  intros v k Hv Hk. unfold Mem.le4. rewrite g2_nth_le_bytes by exact Hk.
  rewrite !Z_to_bv_unsigned.
  rewrite (bv_wrap_small 64 v) by (change (bv_modulus 64) with (2 ^ 64); lia).
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (8 * Z.of_nat 4) with 32. rewrite (Z.mod_small v (2 ^ 32)) by exact Hv. reflexivity.
Qed.
Lemma g2_le_byte1 : forall b : byte, Z_to_bv 8 (YO0f.le_byte (bv_unsigned b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hr. change (bv_modulus 8) with 256 in Hr.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  change (2 ^ (8 * Z.of_nat 1)) with 256. change (8 * Z.of_nat 0) with 0.
  rewrite Z.shiftr_0_r, !(Z.mod_small (bv_unsigned b) 256) by exact Hr. reflexivity.
Qed.
Lemma g2_le_byte0 : forall w k, YO0f.le_byte 0 w k = 0.
Proof.
  intros w k. unfold YO0f.le_byte. rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia).
  rewrite Z.shiftr_0_l. reflexivity.
Qed.
Lemma g2_nth_bzs : forall l n, nth n (bzs l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  unfold bzs. induction l as [|b l IH]; intros [|n]; cbn [map nth]; try reflexivity. apply IH.
Qed.
(* field o of entry i, for o = 0 (fd) and o = 4 (eof) *)
Lemma g2_tbl_fld : forall (W : world segs) (mem : word -> option byte) (G : Z) (es : list rentry)
  (tail : list byte) (i : nat) (o v : Z),
  atable_at W mem G es tail -> Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  (i < length es)%nat -> 0 <= v < 2 ^ 32 ->
  ((o = 0 /\ v = re_fd (nth i es gn_e0)) \/ (o = 4 /\ v = re_eof (nth i es gn_e0))) ->
  val_mem segs (arm W mem) (G + AENT * Z.of_nat i + o) 4 v.
Proof.
  intros W mem G es tail i o v [_ [_ Hg]] Hpad Hi Hv Hfld.
  pose proof (g2_cc_len es Hpad) as Hcl.
  assert (Ho : 0 <= o <= 4) by (destruct Hfld as [[-> _] | [-> _]]; lia).
  unfold val_mem. intros k Hk.
  assert (Hj : (56 * i + (Z.to_nat o + k) < length (bzs (concat (map entry_bytes es) ++ tail)))%nat).
  { unfold bzs. rewrite length_map, length_app, Hcl. lia. }
  unfold garr8 in Hg. destruct (Hg _ Hj) as [Hb _]. unfold val_mem in Hb.
  specialize (Hb 0%nat ltac:(lia)).
  replace (G + AENT * Z.of_nat i + o + Z.of_nat k)
    with (G + Z.of_nat (56 * i + (Z.to_nat o + k)) + Z.of_nat 0) by (unfold AENT; lia).
  rewrite Hb. f_equal.
  assert (Hn : nth (56 * i + (Z.to_nat o + k)) (bzs (concat (map entry_bytes es) ++ tail)) 0 =
               bv_unsigned (nth k (Mem.le4 (Z_to_bv 64 v)) (Z_to_bv 8 0))).
  { rewrite g2_nth_bzs. f_equal.
    rewrite app_nth1 by (rewrite Hcl; lia).
    rewrite g2_cc_nth by (first [exact Hpad | exact Hi | lia]).
    unfold entry_bytes.
    destruct Hfld as [[-> ->] | [-> ->]].
    - change (Z.to_nat 0) with 0%nat. rewrite Nat.add_0_l.
      rewrite app_nth1 by (rewrite Mem.length_le4; exact Hk). reflexivity.
    - change (Z.to_nat 4) with 4%nat.
      rewrite app_nth2 by (rewrite Mem.length_le4; lia). rewrite Mem.length_le4.
      replace (4 + k - 4)%nat with k by lia.
      rewrite app_nth1 by (rewrite Mem.length_le4; exact Hk). reflexivity. }
  rewrite Hn, g2_le_byte1.
  apply bv_eq. rewrite Z_to_bv_unsigned, g2_le4_byte by lia.
  unfold YO0f.le_byte, bv_wrap. change (bv_modulus 8) with 256.
  rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma g2_pads_of_relay : forall ly S W mem G es,
  arelay_at B fr_RG ly S W mem G es ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es /\
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es /\
  Forall (fun e => re_eof e = 0 \/ re_eof e = 1) es.
Proof.
  intros ly S W mem G es (_ & _ & _ & _ & _ & _ & _ & _ & _ & HE & _).
  split; [|split]; rewrite Forall_forall in HE |- *; intros e He;
    destruct (HE e He) as (H1 & _ & H3 & H4 & H5 & _); [split; assumption | exact H5 | exact H1].
Qed.

(* ------------------------------------------------------------------ the bytes of a slot of g_s *)
Lemma g2_zero4 : forall (W : world segs) mem HA off,
  garr8 segs (arm W mem) HA (repeat 0 (Z.to_nat ASRC)) -> 0 <= off -> off + 4 <= ASRC ->
  val_mem segs (arm W mem) (HA + off) 4 0.
Proof.
  intros W mem HA off Hz Hlo Hhi kk Hk.
  destruct (Hz (Z.to_nat (off + Z.of_nat kk))
              ltac:(rewrite repeat_length; unfold ASRC in *; lia)) as [Hb _].
  unfold val_mem in Hb. specialize (Hb 0%nat ltac:(lia)). rewrite nth_repeat in Hb.
  replace (HA + off + Z.of_nat kk) with (HA + Z.of_nat (Z.to_nat (off + Z.of_nat kk)) + Z.of_nat 0) by lia.
  rewrite Hb, !g2_le_byte0. reflexivity.
Qed.
(* the fd and the open flag of slot i, and the model value of each *)
Definition g2_sfd (o : option hsrc) : Z := match o with Some h => hs_fd h | None => 0 end.
Definition g2_sopen (o : option hsrc) : Z := match o with Some _ => 1 | None => 0 end.
Lemma g2_slot_at : forall ly S W mem i o,
  aslot B ly S W mem i o ->
  val_mem segs (arm W mem) (rg_s fr_RG + ASRC * Z.of_nat i) 4 (g2_sfd o) /\
  val_mem segs (arm W mem) (rg_s fr_RG + ASRC * Z.of_nat i + 4) 4 (g2_sopen o) /\
  0 <= g2_sfd o < 2 ^ 31 /\ 0 <= g2_sopen o <= 1.
Proof.
  intros ly S W mem i [h|] Hs; cbn [aslot g2_sfd g2_sopen] in *.
  - pose proof Hs as (H1 & H2 & _ & _ & _ & _ & _ & H8 & H9 & _).
    rewrite H8 in H2. split; [exact H1|]. split; [exact H2|]. split; [exact H9 | lia].
  - destruct Hs as [Hz _].
    pose proof (g2_zero4 W mem (rg_s fr_RG + ASRC * Z.of_nat i) 0 Hz ltac:(lia) ltac:(unfold ASRC; lia)) as H0.
    pose proof (g2_zero4 W mem (rg_s fr_RG + ASRC * Z.of_nat i) 4 Hz ltac:(lia) ltac:(unfold ASRC; lia)) as H4.
    rewrite Z.add_0_r in H0.
    split; [exact H0|]. split; [exact H4|]. split; lia.
Qed.

(* ------------------------------------------------------------------ the index arithmetic of the head.
   The engine folds `slli a0,a2,5; slli a1,a2,7; sub a1,a1,a0` into M_MUL by 96. *)
Lemma g2_U_mul96 : forall (E : env) n m i b,
  ew E n = Z_to_bv 64 i -> 0 <= i < 4 -> ew E m = Z_to_bv 64 b -> 0 <= b -> b + 96 * i + 4 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 96)) (SOff m 0)) = b + 96 * i /\
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff n 0) (SLit 96)) (SLit 4)) (SOff m 0))
    = b + 96 * i + 4.
Proof.
  intros E n m i b Hn Hi Hm Hb Hw.
  assert (HM : U E (SMd M_MUL (SOff n 0) (SLit 96)) = 96 * i).
  { rewrite U_SMd. cbn [zmd_raw]. rewrite (U_atom E n i Hn) by lia. rewrite U_SLit.
    rewrite (zcanon_id 96) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia. }
  split.
  - rewrite U_SAlu. cbn [zalu_raw]. rewrite HM, (U_atom E m b Hm) by lia.
    rewrite zcanon_id by (unfold M64; lia). lia.
  - rewrite !U_SAlu. cbn [zalu_raw]. rewrite HM, (U_atom E m b Hm), U_SLit by lia.
    rewrite (zcanon_id 4) by (unfold M64; lia).
    rewrite (zcanon_id (96 * i + 4)) by (unfold M64; lia).
    rewrite zcanon_id by (unfold M64; lia). lia.
Qed.

(* ------------------------------------------------------------------ the run machinery *)
Let g2_RUN := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let g2_RUNTO := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let g2_BR := paj_branch (PI := PB_fr).
Definition g2_Bx : sv := SOff 26 0.
Definition g2_span : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* after a run over read-only regions, the memory is the one it began in *)
Ltac g2_meq HF Em := lazymatch type of HF with frame_of ?E ?rs ?m ?m' =>
  pose proof (frame_of_read_only E rs m m' ltac:(vm_compute; reflexivity) HF) as Em end.
(* a register of the state after a run, with its symbolic value folded in *)
Ltac g2_reg HS r H :=
  pose proof (st_ok_pi_restrict_reg (PI := PB_fr) _ _ _ _ (r : bv 5) HS) as H;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
    let e := eval vm_compute in (sr_get (ss_regs ss) (r : bv 5)) in
    change (sr_get (ss_regs ss) (r : bv 5)) with e in H end;
  cbn [ms_regs restrict mkst] in H.
Ltac g2_U := apply bv_eq;
  lazymatch goal with |- bv_unsigned (sv_denot ?Ev ?e) = _ => change (bv_unsigned (sv_denot Ev e)) with (U Ev e) end.

(* ------------------------------------------------------------------ (1) 0x84738 -> 0x8474c:
   a1 = &g_s[k], a0 = &g_s[k].open.  Pure ALU: no region, no instrumented check, no store. *)
Definition g2_f_pre : facts :=
  mkFacts [ (12%nat, mkAF 0 3 0); (20%nat, mkAF (rg_s fr_RG) (rg_s fr_RG) 5); (26%nat, mkAF SB SB 0) ] [] [].
Definition g2_ss_pre : sstate := mkSS AF_gn_l1 sr_atoms [] None g2_f_pre.
(* the registers 0x84738-0x84748 leaves alone (it writes a0 and a1 only) *)
Definition G2_KEPT1 : list (bv 5) :=
  [1;2;3;4;5;6;7;8;9;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.
Lemma g2_run1 : forall (W : world segs) regs mem md (q : nat)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk Q,
  (q < 4)%nat ->
  getr regs 12 = w64 (Z.of_nat q) -> getr regs 20 = w64 (rg_s fr_RG) -> getr regs 26 = w64 SB ->
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kk ->
  (forall regs' md',
     ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md' kk ->
     (forall r, In r G2_KEPT1 -> getr regs' r = getr regs r) ->
     getr regs' 11 = w64 (rg_s fr_RG + ASRC * Z.of_nat q) ->
     getr regs' 10 = w64 (rg_s fr_RG + ASRC * Z.of_nat q + 4) ->
     SRr segs W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_gn_sh1)) mem (seg_rom segs)) md') Q) ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_gn_l1)) mem (seg_rom segs)) md) Q.
Proof.
  intros W regs mem md q STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk Q Hq R12 R20 R26 HJ HK.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  assert (HRS : rg_s fr_RG = 6129888) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E12 : ew E 12 = Z_to_bv 64 (Z.of_nat q)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact R12).
  assert (E20 : ew E 20 = Z_to_bv 64 (rg_s fr_RG)) by (rewrite (EEo 20%nat 20%bv eq_refl); exact R20).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (HS : st_ok_pi segs VAL E g2_ss_pre
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_l1)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold g2_ss_pre. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint all_disjoint]. exact I.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_pre f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E12, E20, E26, !unsigned_lit_small by (unfold SB in *; lia).
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia). }
  assert (SHOK : sh_ok segs g2_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
  paj_run_to_tok g2_RUNTO HS HJ SHOK g2_span AF_gn_sh1.
  { apply awr_ok_x_nil. }
  g2_meq HF Em.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_KEPT1 HS HAE
                ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  g2_reg HS (10%bv : bv 5) Q10. g2_reg HS (11%bv : bv 5) Q11.
  pmkst HS. rewrite Em in HJ |- *.
  destruct (g2_U_mul96 E 12%nat 20%nat (Z.of_nat q) (rg_s fr_RG) E12 ltac:(lia) E20
              ltac:(lia) ltac:(rewrite HRS; lia)) as [U11 U10].
  apply (HK (ms_regs ms) _ HJ KR).
  - rewrite Q11. g2_U. rewrite U11. unfold w64. rewrite unsigned_lit_small by (rewrite HRS, HAS; lia).
    rewrite HAS. lia.
  - rewrite Q10. g2_U. rewrite U10. unfold w64. rewrite unsigned_lit_small by (rewrite HRS, HAS; lia).
    rewrite HAS. lia.
Qed.


(* ------------------------------------------------------------------ (2) the INLINED relay_source search
   0x84790-0x847b4, with its found arm 0x847d0-0x847e8 and its empty arm 0x847c8, by induction on the
   entries left.  Each trip restarts the symbolic state with the entry as atom 32: the engine resolves an
   address only as an atom plus a constant, and the latch's `addi a5,a5,7` leaves that shape.  The entry's
   granule is inside the table's 896-byte block, so both instrumented checks (0x84790 of the entry, 0x847d4
   of its eof) are decided inside the run and the arms 0x847b8 / 0x84824 are not reached. *)
Definition g2_sr_scan : list sv :=
  sr_set (sr_set (sr_set sr_atoms 10 (SOff 32 0)) 11 (SOff 32 4))
    15 (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 32 0) (SLit 3))).
Definition g2_rg_scan : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 8 0 0
      [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 4 (CVal 4 (SOff 34 0))] ].
Definition g2_f_scan : facts :=
  mkFacts [ (13%nat, mkAF 1 16 0); (14%nat, mkAF 0 (2 ^ 31 - 1) 0); (26%nat, mkAF SB SB 0);
            (32%nat, mkAF 4096 140737479966720 3); (33%nat, mkAF 0 (2 ^ 31 - 1) 0);
            (34%nat, mkAF 0 1 0) ] [] [].
Definition g2_ss_scan : sstate := mkSS AF_gn_i1 g2_sr_scan g2_rg_scan None g2_f_scan.
Definition g2_SH_scan : list shent := [ mkSHE 32 0 16 ].
Definition g2_x_scan (a u c : Z) : list word := map (Z_to_bv 64) [a; u; c].
(* the registers the search and its two exits leave alone (a0, a1, a3, a5, a6, a7 move) *)
Definition G2_KEPT2 : list (bv 5) :=
  [1;2;3;4;5;6;7;8;9;12;14;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.
(* relay_reads(s) of the entry the search found: eof = 0 *)
Definition g2_srcv (es : list rentry) (fd : Z) : Z :=
  match gn_find es fd 0 with
  | None => 0
  | Some i => if re_eof (nth i es gn_e0) =? 0 then 1 else 0
  end.
Lemma g2_U_seqz : forall (E : env) n v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 31 ->
  U E (SAlu ALU_SLTU (SOff n 0) (SLit 1)) = (if v =? 0 then 1 else 0).
Proof.
  intros E n v Hn Hv. rewrite U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E n v Hn) by lia. rewrite U_SLit.
  rewrite (zcanon_id 1) by (unfold M64; lia).
  destruct (Z.ltb_spec v 1) as [Hlt|Hge].
  - replace (v =? 0) with true by (symmetry; apply Z.eqb_eq; lia).
    rewrite zcanon_id by (unfold M64; lia). reflexivity.
  - replace (v =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
    rewrite zcanon_id by (unfold M64; lia). reflexivity.
Qed.

Lemma g2_scan : forall (k : nat) (j G fd : Z) (es : list rentry) (tail : list byte)
    (W : world segs) regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk Q,
  Z.of_nat k = Z.of_nat (length es) - j -> 0 <= j < Z.of_nat (length es) -> (length es <= 16)%nat ->
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kk ->
  In (G, ATABLE) (ablocks B lyc Sc) ->
  atable_at W mem G es tail ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  Forall (fun e => re_eof e = 0 \/ re_eof e = 1) es ->
  (forall u, (u < Z.to_nat j)%nat -> re_fd (nth u es gn_e0) <> fd) -> 0 <= fd < 2 ^ 31 ->
  getr regs 10 = w64 (G + AENT * j) -> getr regs 11 = w64 (G + AENT * j + 4) ->
  getr regs 13 = w64 (Z.of_nat (length es) - j) -> getr regs 14 = w64 fd ->
  getr regs 15 = w64 (SB + (G + AENT * j) / 8) -> getr regs 26 = w64 SB ->
  (forall regs' md',
     ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md' kk ->
     (forall r, In r G2_KEPT2 -> getr regs' r = getr regs r) ->
     getr regs' 10 = w64 (g2_srcv es fd) ->
     SRr segs W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_gn_v)) mem (seg_rom segs)) md') Q) ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_gn_i1)) mem (seg_rom segs)) md) Q.
Proof.
  induction k as [|k IH];
    intros j G fd es tail W regs mem md STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk Q
      Hk Hj Hlen HJ HGin HTAB HPAD HFDS HEOF HNM Hfd R10 R11 R13 R14 R15 R26 HK; [lia|].
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (ajournal_gx_AR segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kk HJ)
    as HAR.
  destruct (al_blocks _ _ LAWS lyc Sc W mem md G ATABLE HAR HGin) as (HP16 & HP4096 & HPceil & HPapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity.
  rewrite RQ in HPceil, HPapp. pose proof (proj1 HPapp) as HPh.
  assert (G8 : G = 8 * (G / 8)).
  { pose proof (Z.div_mod G 16 ltac:(lia)) as D. rewrite HP16, Z.add_0_r in D.
    rewrite D at 2. replace (16 * (G / 16)) with ((2 * (G / 16)) * 8) by ring.
    rewrite Z.div_mul by lia. lia. }
  assert (XQ : (G + 56 * j) / 8 = G / 8 + 7 * j).
  { rewrite G8 at 1. replace (8 * (G / 8) + 56 * j) with ((G / 8 + 7 * j) * 8) by ring.
    apply Z.div_mul. lia. }
  assert (XQ1 : (G + 56 * (j + 1)) / 8 = G / 8 + 7 * j + 7).
  { rewrite G8 at 1. replace (8 * (G / 8) + 56 * (j + 1)) with ((G / 8 + 7 * j + 7) * 8) by ring.
    apply Z.div_mul. lia. }
  assert (Hjn : (Z.to_nat j < length es)%nat) by lia.
  set (ej := nth (Z.to_nat j) es gn_e0) in *.
  assert (Hfdj : 0 <= re_fd ej < 2 ^ 31)
    by (rewrite Forall_forall in HFDS; apply HFDS; apply nth_In; lia).
  assert (Heofj : re_eof ej = 0 \/ re_eof ej = 1)
    by (rewrite Forall_forall in HEOF; apply HEOF; apply nth_In; lia).
  pose proof (g2_tbl_fld W mem G es tail (Z.to_nat j) 0 (re_fd ej) HTAB HPAD Hjn
                ltac:(lia) ltac:(left; split; reflexivity)) as Mfd.
  pose proof (g2_tbl_fld W mem G es tail (Z.to_nat j) 4 (re_eof ej) HTAB HPAD Hjn
                ltac:(lia) ltac:(right; split; reflexivity)) as Meof.
  rewrite Z2Nat.id in Mfd, Meof by lia. rewrite Z.add_0_r in Mfd.
  unfold AENT in Mfd, Meof, R10, R11, R15.
  remember (Eimg (Ereg regs (g2_x_scan (G + 56 * j) (re_fd ej) (re_eof ej)))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (g2_x_scan (G + 56 * j) (re_fd ej) (re_eof ej))) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E13 : ew E 13 = Z_to_bv 64 (Z.of_nat (length es) - j))
    by (rewrite (EEo 13%nat 13%bv eq_refl); exact R13).
  assert (E14 : ew E 14 = Z_to_bv 64 fd) by (rewrite (EEo 14%nat 14%bv eq_refl); exact R14).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 (G + 56 * j))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 (re_fd ej))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 (re_eof ej))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (USH : U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 32 0) (SLit 3)))
                = SB + (G + 56 * j) / 8).
  { rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 32 _ E32), U_lit by (unfold SB; lia).
    cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
    change (2 ^ 3) with 8. unfold zcanon, M64.
    rewrite XQ. rewrite (Z.mod_small (G / 8 + 7 * j)) by lia.
    rewrite Z.mod_small by (unfold SB; lia). reflexivity. }
  assert (HS : st_ok_pi segs VAL E g2_ss_scan
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_i1)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold g2_ss_scan. apply pa_entry_st_ok_full.
    - unfold g2_sr_scan. rewrite HE.
      apply regs_ok_pin;
        [apply regs_ok_pin; [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
                            | intros X; discriminate X |]
        | intros X; discriminate X |]; rewrite <- HE.
      + rewrite R10. apply bv_eq. fold (U E (SOff 32 0)).
        rewrite (U_atom E 32 _ E32) by lia. apply unsigned_lit_small. lia.
      + rewrite R11. apply bv_eq. fold (U E (SOff 32 4)).
        rewrite (U_atom_off E 32 _ 4 E32) by lia. apply unsigned_lit_small. lia.
      + rewrite R15. apply bv_eq.
        fold (U E (SAlu ALU_ADD (SOff 26 0) (SAlu ALU_SRL (SOff 32 0) (SLit 3)))).
        rewrite USH. apply unsigned_lit_small. unfold SB. lia.
    - vm_compute. reflexivity.
    - unfold g2_rg_scan. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      cbn [base_val]. rewrite E32, unsigned_lit_small by lia.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor; [|constructor]].
      + apply (chunk_ok_val segs E _ (G + 56 * j) 0 4 (SOff 33 0) (re_fd ej));
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mfd.
      + apply (chunk_ok_val segs E _ (G + 56 * j) 4 4 (SOff 34 0) (re_eof ej));
          [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        exact Meof.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_scan f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E13, E14, E26, E32, E33, E34, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia). }
  assert (HBx : U E g2_Bx = SHADOW_OFF)
    by (unfold g2_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs g2_Bx g2_SH_scan E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    + apply (range_addressable_of_block segs B LAWS lyc Sc W mem md G ATABLE (G + 56 * j) 16 HAR HGin);
        rewrite ?RQ; lia.
    + exact HBx.
    + rewrite (U_atom E 32 _ E32) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. lia. }
  (* 0x84790-0x8479c: the entry's instrumented check, its fd, and the match test *)
  paj_run_tok g2_RUN HS HJ SHOK g2_span.
  { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
  g2_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok g2_RUN g2_BR HS SHOK g2_span.
  - (* the entry carries the fd: 0x847d0, its eof, and on to 0x847ec *)
    rewrite branch_eq_U, (U_atom E 33 _ E33), (U_atom E 14 fd E14) in Hc by lia.
    apply Z.eqb_eq in Hc.
    paj_run_to_tok g2_RUNTO HS HJ SHOK g2_span AF_gn_v.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    g2_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_KEPT2 HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (10%bv : bv 5) Q10.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    apply (HK _ _ HJ KR).
    rewrite Q10. g2_U.
    rewrite (g2_U_seqz E 34%nat (re_eof ej) E34 ltac:(lia)).
    unfold g2_srcv.
    rewrite (g2_find_some_from es fd (Z.to_nat j) 0 Hjn ltac:(exact Hc) HNM).
    cbn [Nat.add]. unfold w64.
    rewrite unsigned_lit_small by (destruct (re_eof (nth (Z.to_nat j) es gn_e0) =? 0); lia).
    reflexivity.
  - (* not this entry *)
    rewrite branch_eq_U, (U_atom E 33 _ E33), (U_atom E 14 fd E14) in Hc by lia.
    apply Z.eqb_neq in Hc.
    paj_run_tok g2_RUN HS HJ SHOK g2_span.
    { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
    g2_meq HF Em2. clear HF HFr HG0.
    psrr_branch_tok g2_RUN g2_BR HS SHOK g2_span.
    + (* entries left: back to the head at j + 1 *)
      rewrite branch_ne_U, (U_atom_off E 13 _ (-1) E13), U_lit in Hc0 by lia.
      assert (Hlt : j + 1 < Z.of_nat (length es))
        by (destruct (Z.eqb_spec (Z.of_nat (length es) - j + -1) 0); [discriminate | lia]).
      paj_run_to_tok g2_RUNTO HS HJ SHOK g2_span AF_gn_i1.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      g2_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_KEPT2 HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      g2_reg HS (10%bv : bv 5) N10. g2_reg HS (11%bv : bv 5) N11.
      g2_reg HS (13%bv : bv 5) N13. g2_reg HS (15%bv : bv 5) N15.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      eapply (IH (j + 1) G fd es tail W _ mem _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk Q);
        [ lia | lia | exact Hlen | exact HJ | exact HGin | exact HTAB | exact HPAD | exact HFDS
        | exact HEOF
        | intros u Hu; destruct (Nat.eq_dec u (Z.to_nat j)) as [->|Hne];
            [exact Hc | apply HNM; lia]
        | exact Hfd
        | rewrite N10; g2_U; rewrite (U_atom_off E 32 _ 56 E32) by lia;
            unfold w64, AENT; rewrite unsigned_lit_small by lia; lia
        | rewrite N11; g2_U; rewrite (U_atom_off E 32 _ 60 E32) by lia;
            unfold w64, AENT; rewrite unsigned_lit_small by lia; lia
        | rewrite N13; g2_U; rewrite (U_atom_off E 13 _ (-1) E13) by lia;
            unfold w64; rewrite unsigned_lit_small by lia; lia
        | rewrite (KR 14%bv ltac:(cbv; tauto)); exact R14
        | | rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26
        | intros regs'' md'' HJ'' KR'' Q10'';
          exact (HK regs'' md'' HJ'' ltac:(intros r Hr; rewrite (KR'' r Hr); exact (KR r Hr)) Q10'') ].
      rewrite N15. g2_U.
      rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 32 _ E32), !U_lit by (unfold SB; lia).
      cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
      change (2 ^ 3) with 8. unfold zcanon, M64.
      rewrite XQ, (Z.mod_small (G / 8 + 7 * j)) by lia.
      rewrite (Z.mod_small (SB + (G / 8 + 7 * j))) by (unfold SB; lia).
      rewrite Z.mod_small by (unfold SB; lia).
      unfold w64, AENT.
      rewrite XQ1.
      rewrite unsigned_lit_small by (unfold SB; lia). lia.
    + (* no entry left: the search failed, 0x847c8 sets a0 = 0 *)
      rewrite branch_ne_U, (U_atom_off E 13 _ (-1) E13), U_lit in Hc0 by lia.
      assert (Hend : j + 1 = Z.of_nat (length es))
        by (destruct (Z.eqb_spec (Z.of_nat (length es) - j + -1) 0); [lia | discriminate]).
      paj_run_to_tok g2_RUNTO HS HJ SHOK g2_span AF_gn_v.
      { apply awr_ok_x_cons; [intros a Ha; cbn in Ha; lia | apply awr_ok_x_nil]. }
      g2_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_KEPT2 HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      g2_reg HS (10%bv : bv 5) Q10.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      apply (HK _ _ HJ KR).
      rewrite Q10. unfold g2_srcv.
      rewrite (g2_find_none_from es fd 0
                 ltac:(intros u Hu; destruct (Nat.eq_dec u (Z.to_nat j)) as [->|Hne];
                       [exact Hc | apply HNM; lia])).
      cbn [sv_denot]. unfold w64. reflexivity.
Qed.

(* ------------------------------------------------------------------ (3) 0x8474c -> 0x847ec: the two
   instrumented checks of the slot, g_s[k].open, g_nsrc, g_src and the search.  Restarted with the slot as
   atom 32: its granules lie in g_s's zero-shadow range, so both checks are decided inside the run and the
   arms 0x84804 / 0x84814 are not reached. *)
Definition g2_sr_body : list sv :=
  sr_set (sr_set (sr_set (sr_set sr_atoms 10 (SOff 32 4)) 11 (SOff 32 0))
    23 (SOff (A_HI 74) 0)) 18 (SOff (A_HI 75) 0).
Definition g2_rg_body : smem :=
  [ YP09.mkRegion (Some 32%nat) 0 8 0 0
      [YP09.mkChunk 0 (CVal 4 (SOff 33 0)); YP09.mkChunk 4 (CVal 4 (SOff 34 0))];
    YP09.mkRegion (Some (A_OBJ 7)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 35 0))];
    YP09.mkRegion (Some (A_OBJ 8)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 36 0))] ].
Definition g2_f_body : facts :=
  mkFacts [ (26%nat, mkAF SB SB 0); (32%nat, mkAF (rg_s fr_RG) (rg_s fr_RG + 3 * ASRC) 5);
            (33%nat, mkAF 0 (2 ^ 31 - 1) 0); (34%nat, mkAF 0 1 0); (35%nat, mkAF 0 16 0);
            (36%nat, mkAF 4096 140737479966720 4) ] [] [].
Definition g2_ss_body : sstate := mkSS AF_gn_sh1 g2_sr_body g2_rg_body None g2_f_body.
Definition g2_SH_body : list shent := [ mkSHE 32 0 ASRC ].
Definition g2_x_body (a u o n t : Z) : list word := map (Z_to_bv 64) [a; u; o; n; t].
(* the registers the block leaves alone (a0, a1, a3, a4, a5, a6, a7 move; s2 and s7 hold image atoms) *)
Definition G2_KEPT3 : list (bv 5) :=
  [1;2;3;4;5;6;7;8;9;12;19;20;21;22;24;25;26;27;28;29;30;31]%bv.
Lemma g2_hi : VAL (A_HI 74) = HI_G_NSRC /\ VAL (A_HI 75) = HI_G_SRC /\
  VAL (A_OBJ 7) = rg_nsrc fr_RG /\ VAL (A_OBJ 8) = rg_src fr_RG.
Proof. vm_compute. repeat split. Qed.

Lemma g2_run2 : forall (W : world segs) regs mem md (A fd open G : Z) (es : list rentry) (tail : list byte)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk Q,
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kk ->
  In (G, ATABLE) (ablocks B lyc Sc) ->
  atable_at W mem G es tail ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat) es ->
  Forall (fun e => 0 <= re_fd e < 2 ^ 31) es ->
  Forall (fun e => re_eof e = 0 \/ re_eof e = 1) es ->
  (length es <= 16)%nat ->
  val_mem segs (arm W mem) (rg_nsrc fr_RG) 4 (Z.of_nat (length es)) ->
  val_mem segs (arm W mem) (rg_src fr_RG) 8 G ->
  azs B A ASRC ->
  val_mem segs (arm W mem) A 4 fd -> 0 <= fd < 2 ^ 31 ->
  val_mem segs (arm W mem) (A + 4) 4 open -> 0 <= open <= 1 ->
  rg_s fr_RG <= A -> A + ASRC <= rg_s fr_RG + 4 * ASRC -> A mod 32 = 0 ->
  getr regs 11 = w64 A -> getr regs 10 = w64 (A + 4) ->
  getr regs 18 = w64 HI_G_SRC -> getr regs 23 = w64 HI_G_NSRC -> getr regs 26 = w64 SB ->
  (forall regs' md',
     ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md' kk ->
     (forall r, In r G2_KEPT3 -> getr regs' r = getr regs r) ->
     getr regs' 18 = w64 HI_G_SRC -> getr regs' 23 = w64 HI_G_NSRC ->
     getr regs' 10 = w64 (if open =? 0 then 0 else g2_srcv es fd) ->
     SRr segs W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + AF_gn_v)) mem (seg_rom segs)) md') Q) ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_gn_sh1)) mem (seg_rom segs)) md) Q.
Proof.
  intros W regs mem md A fd open G es tail STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk Q
    HJ HGin HTAB HPAD HFDS HEOF Hlen Mnsrc Msrc HZSA Mfd Hfd Mopen Hopen HA1 HA2 HA32
    R11 R10 R18 R23 R26 HK.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (ajournal_gx_AR segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kk HJ)
    as HAR.
  destruct (al_blocks _ _ LAWS lyc Sc W mem md G ATABLE HAR HGin) as (HP16 & HP4096 & HPceil & HPapp & _).
  assert (RQ : req_size ATABLE = 896) by reflexivity.
  rewrite RQ in HPceil, HPapp.
  assert (HRS : rg_s fr_RG = 6129888) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  assert (HVN : rg_nsrc fr_RG = 6129568) by reflexivity.
  assert (HVG : rg_src fr_RG = 6129600) by reflexivity.
  assert (G8 : 0 <= G / 8 /\ 8 * (G / 8) <= G)
    by (split; [apply Z.div_pos; lia | apply Z.mul_div_le; lia]).
  remember (Eimg (Ereg regs (g2_x_body A fd open (Z.of_nat (length es)) G))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (g2_x_body A fd open (Z.of_nat (length es)) G)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (E32 : ew E 32 = Z_to_bv 64 A)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 fd)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 open)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E35 : ew E 35 = Z_to_bv 64 (Z.of_nat (length es)))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
  assert (E36 : ew E 36 = Z_to_bv 64 G)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 4)).
  assert (EH74 : ew E 354 = Z_to_bv 64 HI_G_NSRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia);
        exact (f_equal (Z_to_bv 64) (proj1 g2_hi))).
  assert (EH75 : ew E 355 = Z_to_bv 64 HI_G_SRC)
    by (subst E; rewrite Eimg_img by (unfold A_TEXT, A_LIM; lia);
        exact (f_equal (Z_to_bv 64) (proj1 (proj2 g2_hi)))).
  assert (EO7 : ew E (A_OBJ 7) = Z_to_bv 64 (rg_nsrc fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj1 (proj2 (proj2 g2_hi))); reflexivity).
  assert (EO8 : ew E (A_OBJ 8) = Z_to_bv 64 (rg_src fr_RG))
    by (subst E; rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia);
        rewrite (proj2 (proj2 (proj2 g2_hi))); reflexivity).
  assert (U32 : bv_unsigned (ew E 32) = A) by (rewrite E32; apply unsigned_lit_small; lia).
  assert (UO7 : bv_unsigned (ew E (A_OBJ 7)) = rg_nsrc fr_RG)
    by (rewrite EO7; apply unsigned_lit_small; rewrite HVN; lia).
  assert (UO8 : bv_unsigned (ew E (A_OBJ 8)) = rg_src fr_RG)
    by (rewrite EO8; apply unsigned_lit_small; rewrite HVG; lia).
  assert (HS : st_ok_pi segs VAL E g2_ss_body
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_sh1)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold g2_ss_body. apply pa_entry_st_ok_full.
    - unfold g2_sr_body. rewrite HE.
      apply regs_ok_pin;
        [apply regs_ok_pin;
          [apply regs_ok_pin;
            [apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | intros X; discriminate X |]
            | intros X; discriminate X |]
          | intros X; discriminate X |]
        | intros X; discriminate X |]; rewrite <- HE.
      + rewrite R10. apply bv_eq. fold (U E (SOff 32 4)).
        rewrite (U_atom_off E 32 A 4 E32) by lia. apply unsigned_lit_small. lia.
      + rewrite R11. apply bv_eq. fold (U E (SOff 32 0)).
        rewrite (U_atom E 32 A E32) by lia. apply unsigned_lit_small. lia.
      + rewrite R23. apply bv_eq. fold (U E (SOff (A_HI 74) 0)).
        rewrite (U_img_atom E HEI (A_HI 74)) by (unfold A_HI, A_TEXT, A_LIM; lia).
        rewrite (proj1 g2_hi). unfold w64. apply unsigned_lit_small. unfold HI_G_NSRC; lia.
      + rewrite R18. apply bv_eq. fold (U E (SOff (A_HI 75) 0)).
        rewrite (U_img_atom E HEI (A_HI 75)) by (unfold A_HI, A_TEXT, A_LIM; lia).
        rewrite (proj1 (proj2 g2_hi)). unfold w64. apply unsigned_lit_small. unfold HI_G_SRC; lia.
    - vm_compute. reflexivity.
    - unfold g2_rg_body. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      + rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor; [|constructor]].
        * apply (chunk_ok_val segs E _ A 0 4 (SOff 33 0) fd);
            [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          rewrite Z.add_0_r. exact Mfd.
        * apply (chunk_ok_val segs E _ A 4 4 (SOff 34 0) open);
            [cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
          exact Mopen.
      + rewrite UO7. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_nsrc fr_RG) 0 4 (SOff 35 0) (Z.of_nat (length es)));
          [cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Mnsrc.
      + rewrite UO8. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (rg_src fr_RG) 0 8 (SOff 36 0) G);
          [cbn [sv_denot]; rewrite E36, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact Msrc.
    - apply pairwise_disjoint_of_extents. unfold g2_rg_body, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U32, UO7, UO8.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      rewrite HRS, HAS, HVN, HVG in *. repeat split; lia.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_body f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E26, E32, E33, E34, E35, E36, !unsigned_lit_small by (unfold SB in *; lia).
      change (2 ^ 5) with 32. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia). }
  assert (HBx : U E g2_Bx = SHADOW_OFF)
    by (unfold g2_Bx; rewrite (U_atom E 26 SB E26) by (unfold SB; lia); reflexivity).
  assert (SHOK : sh_ok segs g2_Bx g2_SH_body E (mrestrict (w_H W) mem)).
  { constructor; [|constructor].
    eapply shent_ok_of_range.
    + exact (azs_range_addressable B LAWS lyc Sc W mem md A ASRC HAR HZSA).
    + exact HBx.
    + rewrite (U_atom E 32 A E32) by lia. reflexivity.
    + lia.
    + lia.
    + intros x Hx. unfold SHADOW_OFF in *. rewrite HRS, HAS in *. cbn [Z.min Z.max] in Hx. lia. }
  (* 0x8474c-0x84760: the check of &g_s[k].open, the load, and the open test *)
  paj_run_tok g2_RUN HS HJ SHOK g2_span.
  { repeat (apply awr_ok_x_cons; [intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | ]). apply awr_ok_x_nil. }
  g2_meq HF Em1. clear HF HFr HG0.
  psrr_branch_tok g2_RUN g2_BR HS SHOK g2_span.
  - (* the slot is closed: reads[k] = 0 *)
    rewrite branch_eq_U, (U_atom E 34 open E34), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc.
    paj_run_to_tok g2_RUNTO HS HJ SHOK g2_span AF_gn_v.
    { repeat (apply awr_ok_x_cons; [intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | ]). apply awr_ok_x_nil. }
    g2_meq HF Em2.
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_KEPT3 HS HAE
                  ltac:(vm_compute; reflexivity)) as KR.
    cbn [ms_regs restrict] in KR.
    g2_reg HS (10%bv : bv 5) Q10.
    pmkst HS. rewrite Em2, Em1 in HJ |- *.
    prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23.
    rewrite EH75 in Q18. rewrite EH74 in Q23.
    apply (HK _ _ HJ KR); [exact Q18 | exact Q23 |].
    rewrite Q10. rewrite Hc. cbn [Z.eqb]. g2_U.
    rewrite (U_atom E 34 open E34) by lia. rewrite Hc. unfold w64. reflexivity.
  - (* the slot is open *)
    rewrite branch_eq_U, (U_atom E 34 open E34), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    assert (Hof : (open =? 0) = false) by (apply Z.eqb_neq; exact Hc).
    (* 0x84764-0x84778: the check of &g_s[k], g_nsrc, and the empty-table test *)
    paj_run_tok g2_RUN HS HJ SHOK g2_span.
    { repeat (apply awr_ok_x_cons; [intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | ]). apply awr_ok_x_nil. }
    g2_meq HF Em2. clear HF HFr HG0.
    lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
      assert (S35 : bv_signed (sv_denot Ev (SOff 35 0)) = Z.of_nat (length es))
        by (assert (U35 : U Ev (SOff 35 0) = Z.of_nat (length es))
              by (apply U_atom; [rewrite ?ew_ewset_other by lia; exact E35 | lia]);
            unfold U in U35; rewrite bv_signed_small; [exact U35 | rewrite U35; lia]);
      assert (S0 : bv_signed (sv_denot Ev (SLit 0)) = 0) by reflexivity
    end.
    psrr_branch_tok g2_RUN g2_BR HS SHOK g2_span.
    + (* the table is empty: reads[k] = 0 *)
      cbn [branch_taken] in Hc0. rewrite bv_lts_signed, S0, S35 in Hc0.
      apply Bool.negb_true_iff, Z.ltb_ge in Hc0.
      assert (Hnil : es = []) by (destruct es; [reflexivity | cbn [length] in Hc0; lia]).
      paj_run_to_tok g2_RUNTO HS HJ SHOK g2_span AF_gn_v.
      { repeat (apply awr_ok_x_cons; [intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | ]). apply awr_ok_x_nil. }
      g2_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_KEPT3 HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      g2_reg HS (10%bv : bv 5) Q10.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23.
      rewrite EH75 in Q18. rewrite EH74 in Q23.
      apply (HK _ _ HJ KR); [exact Q18 | exact Q23 |].
      rewrite Q10, Hnil, Hof. unfold g2_srcv. cbn [gn_find]. cbn [sv_denot]. unfold w64. reflexivity.
    + (* the table has entries: the search, from entry 0 *)
      cbn [branch_taken] in Hc0. rewrite bv_lts_signed, S0, S35 in Hc0.
      apply Bool.negb_false_iff, Z.ltb_lt in Hc0.
      paj_run_to_tok g2_RUNTO HS HJ SHOK g2_span AF_gn_i1.
      { repeat (apply awr_ok_x_cons; [intros a Ha;
          cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia | ]). apply awr_ok_x_nil. }
      g2_meq HF Em3.
      pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_KEPT3 HS HAE
                    ltac:(vm_compute; reflexivity)) as KR.
      cbn [ms_regs restrict] in KR.
      g2_reg HS (10%bv : bv 5) N10. g2_reg HS (11%bv : bv 5) N11.
      g2_reg HS (13%bv : bv 5) N13. g2_reg HS (14%bv : bv 5) N14.
      g2_reg HS (15%bv : bv 5) N15.
      prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23.
      rewrite EH75 in Q18. rewrite EH74 in Q23.
      pmkst HS. rewrite Em3, Em2, Em1 in HJ |- *.
      eapply (g2_scan (length es) 0 G fd es tail W _ mem _ STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk Q);
        [ lia | lia | exact Hlen | exact HJ | exact HGin | exact HTAB | exact HPAD | exact HFDS
        | exact HEOF
        | intros u Hu; cbn in Hu; lia
        | exact Hfd
        | rewrite N10; g2_U; rewrite ?ew_ewset_other by lia;
            rewrite (U_atom E 36 G E36) by lia; unfold w64, AENT;
            rewrite unsigned_lit_small by lia; lia
        | rewrite N11; g2_U; rewrite ?ew_ewset_other by lia;
            rewrite (U_atom_off E 36 G 4 E36) by lia; unfold w64, AENT;
            rewrite unsigned_lit_small by lia; lia
        | rewrite N13; g2_U; rewrite ?ew_ewset_other by lia;
            rewrite (U_atom E 35 _ E35) by lia; unfold w64;
            rewrite unsigned_lit_small by lia; lia
        | rewrite N14; g2_U; rewrite ?ew_ewset_other by lia;
            rewrite (U_atom E 33 fd E33) by lia; unfold w64;
            rewrite unsigned_lit_small by lia; lia
        | | rewrite (KR 26%bv ltac:(cbv; tauto)); exact R26
        | intros regs'' md'' KJ'' KR'' Q10'';
          apply (HK regs'' md'' KJ''
                   ltac:(intros r Hr; rewrite (KR'' r ltac:(cbv [G2_KEPT3 G2_KEPT2 In] in Hr |- *;
                                                            tauto)); exact (KR r Hr)));
          [ rewrite (KR'' 18%bv ltac:(cbv; tauto)); exact Q18
          | rewrite (KR'' 23%bv ltac:(cbv; tauto)); exact Q23
          | rewrite Q10'', Hof; reflexivity ] ].
      rewrite N15. g2_U. rewrite ?ew_ewset_other by lia.
      rewrite !U_SAlu, (U_atom E 26 SB E26), (U_atom E 36 G E36), !U_lit by (unfold SB; lia).
      cbn [zalu_raw]. change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia.
      change (2 ^ 3) with 8. unfold zcanon, M64.
      rewrite (Z.mod_small (G / 8)) by lia.
      rewrite (Z.mod_small (SB + G / 8)) by (unfold SB; lia).
      unfold w64, AENT. rewrite Z.mul_0_r, Z.add_0_r.
      rewrite unsigned_lit_small by (unfold SB; lia). lia.
Qed.

(* ------------------------------------------------------------------ (4) 0x847ec -> 0x84738 / 0x84834:
   `sw a0,0(a1)` writes reads[k] into the caller's own frame cell F + 192 + 4k (no instrumented check: the
   cell is in the function's stack window), `addi a2,a2,1`, and the latch leaves the loop at k + 1 = 4.
   Restarted at 0x847f8 so that the store's address is an atom. *)
Definition g2_f_pv : facts :=
  mkFacts [ (5%nat, mkAF 4 4 0); (6%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (12%nat, mkAF 0 3 0);
            (26%nat, mkAF SB SB 0) ] [] [].
Definition g2_ss_pv : sstate := mkSS AF_gn_v sr_atoms [] None g2_f_pv.
Definition g2_rg_tail : smem := [ YP09.mkRegion (Some 11%nat) 0 4 0 4 [] ].
Definition g2_f_tail : facts :=
  mkFacts [ (5%nat, mkAF 4 4 0); (11%nat, mkAF (2 ^ 46) (2 ^ 47) 2); (12%nat, mkAF 1 4 0);
            (26%nat, mkAF SB SB 0) ] [] [].
Definition g2_ss_tail : sstate := mkSS AF_gn_sw sr_atoms g2_rg_tail None g2_f_tail.
(* the registers 0x847ec-0x847fc leaves alone (a1 and a2 move) *)
Definition G2_KEPT4 : list (bv 5) :=
  [1;2;3;4;5;6;7;8;9;10;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31]%bv.

Lemma g2_run3 : forall (W : world segs) regs mem md (F v : Z) (q : nat)
    STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk Q,
  ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md kk ->
  (q < 4)%nat -> 2 ^ 46 <= F -> F + 216 <= 2 ^ 47 -> F mod 32 = 0 -> 0 <= v <= 1 ->
  sp0 - STK <= F + 192 -> F + 208 <= sp0 ->
  (forall a, F + 192 <= a < F + 208 -> writable_at segs (arm W mem) a) ->
  getr regs 10 = w64 v -> getr regs 12 = w64 (Z.of_nat q) -> getr regs 5 = w64 4 ->
  getr regs 6 = w64 (F + 192) -> getr regs 26 = w64 SB ->
  (forall regs' mem' md' (pc : Z),
     ((pc = AF_gn_l1 /\ (q < 3)%nat) \/ (pc = AF_gn_rig /\ q = 3%nat)) ->
     ajournal_gx segs B G_fr 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem' md' kk ->
     (forall r, In r G2_KEPT4 -> getr regs' r = getr regs r) ->
     getr regs' 12 = w64 (Z.of_nat q + 1) ->
     val_mem segs (arm W mem') (F + 192 + 4 * Z.of_nat q) 4 v ->
     (forall a, 0 <= a < 2 ^ 64 ->
        ~ (F + 192 + 4 * Z.of_nat q <= a < F + 192 + 4 * Z.of_nat q + 4) -> abyte_kept W mem W mem' a) ->
     (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
     SRr segs W (mkCfg (mkst regs' (Z_to_bv 64 (BASE + pc)) mem' (seg_rom segs)) md') Q) ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + AF_gn_v)) mem (seg_rom segs)) md) Q.
Proof.
  intros W regs mem md F v q STK sp0 FP ly S W0 mem0 md0 own lyc Sc kk Q
    HJ Hq HF1 HF2 HF32 Hv Hs1 Hs2 HW R10 R12 R5 R6 R26 HK.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
  (* ---- 0x847ec-0x847f4: a1 = F + 192 + 4k, a2 = k + 1 (pure ALU) ---- *)
  remember (Eimg (Ereg regs (@nil word))) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs (@nil word)) E)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew E n = getr regs rr)
    by (intros n rr Hn; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E5 : ew E 5 = Z_to_bv 64 4) by (rewrite (EEo 5%nat 5%bv eq_refl); exact R5).
  assert (E6 : ew E 6 = Z_to_bv 64 (F + 192)) by (rewrite (EEo 6%nat 6%bv eq_refl); exact R6).
  assert (E12 : ew E 12 = Z_to_bv 64 (Z.of_nat q)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact R12).
  assert (E26 : ew E 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26).
  assert (HS : st_ok_pi segs VAL E g2_ss_pv
                 (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + AF_gn_v)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold g2_ss_pv. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - apply Forall_nil.
    - cbn [pairwise_disjoint all_disjoint]. exact I.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_pv f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E5, E6, E12, E26, !unsigned_lit_small by (unfold SB in *; lia).
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia). }
  assert (SHOK : sh_ok segs g2_Bx (@nil shent) E (mrestrict (w_H W) mem)) by constructor.
  paj_run_to_tok g2_RUNTO HS HJ SHOK g2_span AF_gn_sw.
  { apply awr_ok_x_nil. }
  g2_meq HF Em1.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs _ G2_KEPT4 HS HAE
                ltac:(vm_compute; reflexivity)) as KR1.
  cbn [ms_regs restrict] in KR1.
  g2_reg HS (11%bv : bv 5) P11. g2_reg HS (12%bv : bv 5) P12.
  assert (V11 : getr (ms_regs ms) 11 = w64 (F + 192 + 4 * Z.of_nat q)).
  { rewrite P11. g2_U.
    rewrite !U_SAlu, (U_atom E 6 _ E6), (U_atom E 12 _ E12), U_lit by lia. cbn [zalu_raw].
    change (Z.land 2 63) with 2. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 2) with 4.
    unfold zcanon, M64. rewrite (Z.mod_small (Z.of_nat q * 4)) by lia.
    rewrite Z.mod_small by lia. unfold w64. rewrite unsigned_lit_small by lia. lia. }
  assert (V12 : getr (ms_regs ms) 12 = w64 (Z.of_nat q + 1)).
  { rewrite P12. g2_U. rewrite (U_atom_off E 12 _ 1 E12) by lia.
    unfold w64. rewrite unsigned_lit_small by lia. lia. }
  pmkst HS. rewrite Em1 in HJ |- *.
  clear HS SHOK HE HAE HEI EEo E5 E6 E12 E26 P11 P12 HF HFr HG0.
  (* ---- 0x847f8-0x847fc: the store of reads[k] and the latch ---- *)
  set (regs1 := ms_regs ms) in *.
  assert (R5' : getr regs1 5 = w64 4) by (rewrite (KR1 5%bv ltac:(cbv; tauto)); exact R5).
  assert (R10' : getr regs1 10 = w64 v) by (rewrite (KR1 10%bv ltac:(cbv; tauto)); exact R10).
  assert (R26' : getr regs1 26 = w64 SB) by (rewrite (KR1 26%bv ltac:(cbv; tauto)); exact R26).
  remember (Eimg (Ereg regs1 (@nil word))) as Eb eqn:HE.
  assert (HEI : img_env VAL A_LIM Eb) by (subst Eb; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs1 (@nil word)) Eb)
    by (rewrite HE; split; [intros n Hn; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (EEo : forall n (rr : bv 5), Z.of_nat n = bv_unsigned rr -> ew Eb n = getr regs1 rr)
    by (intros n rr Hn; subst Eb; pose proof (bv_unsigned_in_range 5 rr) as Hr5;
        change (bv_modulus 5) with 32 in Hr5; rewrite Eimg_low by (unfold A_TEXT; lia);
        apply ew_Ereg_nat; exact Hn).
  assert (E5 : ew Eb 5 = Z_to_bv 64 4) by (rewrite (EEo 5%nat 5%bv eq_refl); exact R5').
  assert (E10 : ew Eb 10 = Z_to_bv 64 v) by (rewrite (EEo 10%nat 10%bv eq_refl); exact R10').
  assert (E11 : ew Eb 11 = Z_to_bv 64 (F + 192 + 4 * Z.of_nat q))
    by (rewrite (EEo 11%nat 11%bv eq_refl); exact V11).
  assert (E12 : ew Eb 12 = Z_to_bv 64 (Z.of_nat q + 1)) by (rewrite (EEo 12%nat 12%bv eq_refl); exact V12).
  assert (E26 : ew Eb 26 = Z_to_bv 64 SB) by (rewrite (EEo 26%nat 26%bv eq_refl); exact R26').
  assert (U11 : bv_unsigned (ew Eb 11) = F + 192 + 4 * Z.of_nat q)
    by (rewrite E11; apply unsigned_lit_small; lia).
  assert (HS : st_ok_pi segs VAL Eb g2_ss_tail
                 (restrict (w_H W) (mkst regs1 (Z_to_bv 64 (BASE + AF_gn_sw)) mem (seg_rom segs)))).
  { rewrite restrict_mkst_fx. unfold g2_ss_tail. apply pa_entry_st_ok_full.
    - rewrite HE. apply regs_ok_Eimg_Ereg.
    - vm_compute. reflexivity.
    - unfold g2_rg_tail. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
        cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U11. split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
      intros o Ho. apply HW. lia.
    - cbn [pairwise_disjoint all_disjoint]. repeat split.
    - split; [|split; [exact I | exact I]].
      cbn [g2_f_tail f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E5, E11, E12, E26, !unsigned_lit_small by (unfold SB in *; lia).
      change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
      repeat match goal with |- _ /\ _ => split end; try (unfold SB; lia). }
  assert (SHOK : sh_ok segs g2_Bx (@nil shent) Eb (mrestrict (w_H W) mem)) by constructor.
  paj_run_tok g2_RUN HS HJ SHOK g2_span.
  { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite U11 in Ha.
    left. split; [left; lia | lia]. }
  rename HF into HFst, HFr into HFrst, HG0 into HGst.
  (* a byte present before a run that only grows the memory is present after it *)
  assert (PG : forall (m m' : word -> option byte) a,
      mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') ->
      apresent (w_H W) m a -> apresent (w_H W) m' a).
  { intros m m' a Hgr [Hh [b Hb]]. split; [exact Hh|].
    specialize (Hgr (Z_to_bv 64 a)). unfold mrestrict in Hgr. rewrite Hh in Hgr.
    destruct (m' (Z_to_bv 64 a)) as [b'|] eqn:Em; [exists b'; reflexivity|].
    exfalso. apply Hgr; [rewrite Hb; discriminate | reflexivity]. }
  assert (KEEP0 : forall a, 0 <= a < 2 ^ 64 ->
      ~ (F + 192 + 4 * Z.of_nat q <= a < F + 192 + 4 * Z.of_nat q + 4) ->
      abyte_kept W mem W (ms_mem ms0) a).
  { intros a Ha Hna. split.
    - apply (aview_kept_out _ _ _ _ _ HFrst a Ha).
      intros (r & Hin & Hr). cbn [ss_mem g2_ss_tail g2_rg_tail In] in Hin.
      destruct Hin as [<- | []].
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite U11 in Hr. lia.
    - intros Hw. exact (writable_kept (w_H W) mem (ms_mem ms0) a (PG _ _ a HGst) Hw). }
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs1 _ G2_KEPT4 HS HAE
                ltac:(vm_compute; reflexivity)) as KR2.
  cbn [ms_regs restrict] in KR2.
  assert (KR : forall r, In r G2_KEPT4 -> getr (ms_regs ms0) r = getr regs r)
    by (intros r Hr; rewrite (KR2 r Hr); exact (KR1 r Hr)).
  psrr_branch_tok g2_RUN g2_BR HS SHOK g2_span.
  - (* k + 1 <> 4: back to the loop's head *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom _ 12 _ ltac:(rewrite ?ew_ewset_other by lia; exact E12)) in Hc by lia.
    rewrite (U_atom _ 5 4 ltac:(rewrite ?ew_ewset_other by lia; exact E5)) in Hc by lia.
    apply Bool.negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok g2_RUNTO HS HJ SHOK g2_span AF_gn_l1.
    { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
      intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite ?ew_ewset_other in Ha by lia. rewrite U11 in Ha.
      left. split; [left; lia | lia]. }
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    assert (MV0 : val_mem segs (mrestrict (w_H W) (ms_mem ms1))
                    (F + 192 + 4 * Z.of_nat q + 0) (N.to_nat 4) v).
    { lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 11%nat (F + 192 + 4 * Z.of_nat q) _ _ _ _ _ 0 4%N (SOff 10 0) v RG1)
      end.
      - rewrite ?ew_ewset_other by lia. exact U11.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite ?ew_ewset_other by lia.
        rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    assert (MV : val_mem segs (arm W (ms_mem ms1)) (F + 192 + 4 * Z.of_nat q) 4 v)
      by (unfold arm; rewrite Z.add_0_r in MV0; change (N.to_nat 4) with 4%nat in MV0; exact MV0).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
        ~ (F + 192 + 4 * Z.of_nat q <= a < F + 192 + 4 * Z.of_nat q + 4) ->
        abyte_kept W mem W (ms_mem ms1) a).
    { intros a Ha Hna. split.
      - rewrite (aview_kept_out _ _ _ _ _ HFr a Ha)
          by (intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []];
              cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
              rewrite ?ew_ewset_other in Hr by lia; rewrite U11 in Hr; lia).
        exact (proj1 (KEEP0 a Ha Hna)).
      - intros Hw. exact (writable_kept (w_H W) (ms_mem ms0) (ms_mem ms1) a (PG _ _ a HG0)
                            (proj2 (KEEP0 a Ha Hna) Hw)). }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms1)) a)
      by (intros a Hw; exact (writable_kept (w_H W) (ms_mem ms0) (ms_mem ms1) a (PG _ _ a HG0)
                                (writable_kept (w_H W) mem (ms_mem ms0) a (PG _ _ a HGst) Hw))).
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs1 _ G2_KEPT4 HS HAE
                  ltac:(vm_compute; reflexivity)) as KR3.
    cbn [ms_regs restrict] in KR3.
    g2_reg HS (12%bv : bv 5) M12.
    pmkst HS.
    apply (HK _ _ _ AF_gn_l1 ltac:(left; split; [reflexivity | lia]) HJ
             ltac:(intros r Hr; rewrite (KR3 r Hr); exact (KR1 r Hr))); [| exact MV | exact KEEP | exact WK].
    rewrite M12. g2_U. rewrite ?ew_ewset_other by lia.
    rewrite (U_atom Eb 12 _ E12) by lia. unfold w64. rewrite unsigned_lit_small by lia. lia.
  - (* k + 1 = 4: 0x84800 `j 0x84834`, the call *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom _ 12 _ ltac:(rewrite ?ew_ewset_other by lia; exact E12)) in Hc by lia.
    rewrite (U_atom _ 5 4 ltac:(rewrite ?ew_ewset_other by lia; exact E5)) in Hc by lia.
    apply Bool.negb_false_iff, Z.eqb_eq in Hc.
    paj_run_to_tok g2_RUNTO HS HJ SHOK g2_span AF_gn_rig.
    { apply awr_ok_x_cons; [| apply awr_ok_x_nil].
      intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
      rewrite ?ew_ewset_other in Ha by lia. rewrite U11 in Ha.
      left. split; [left; lia | lia]. }
    pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RG1. cbn [ms_mem restrict] in RG1.
    assert (MV0 : val_mem segs (mrestrict (w_H W) (ms_mem ms1))
                    (F + 192 + 4 * Z.of_nat q + 0) (N.to_nat 4) v).
    { lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
        apply (field_of_region Ev _ 11%nat (F + 192 + 4 * Z.of_nat q) _ _ _ _ _ 0 4%N (SOff 10 0) v RG1)
      end.
      - rewrite ?ew_ewset_other by lia. exact U11.
      - left. reflexivity.
      - cbn [sv_denot]. rewrite ?ew_ewset_other by lia.
        rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
      - zside.
      - zside. }
    assert (MV : val_mem segs (arm W (ms_mem ms1)) (F + 192 + 4 * Z.of_nat q) 4 v)
      by (unfold arm; rewrite Z.add_0_r in MV0; change (N.to_nat 4) with 4%nat in MV0; exact MV0).
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 ->
        ~ (F + 192 + 4 * Z.of_nat q <= a < F + 192 + 4 * Z.of_nat q + 4) ->
        abyte_kept W mem W (ms_mem ms1) a).
    { intros a Ha Hna. split.
      - rewrite (aview_kept_out _ _ _ _ _ HFr a Ha)
          by (intros (r & Hin & Hr); cbn [In] in Hin; destruct Hin as [<- | []];
              cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
              rewrite ?ew_ewset_other in Hr by lia; rewrite U11 in Hr; lia).
        exact (proj1 (KEEP0 a Ha Hna)).
      - intros Hw. exact (writable_kept (w_H W) (ms_mem ms0) (ms_mem ms1) a (PG _ _ a HG0)
                            (proj2 (KEEP0 a Ha Hna) Hw)). }
    assert (WK : forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W (ms_mem ms1)) a)
      by (intros a Hw; exact (writable_kept (w_H W) (ms_mem ms0) (ms_mem ms1) a (PG _ _ a HG0)
                                (writable_kept (w_H W) mem (ms_mem ms0) a (PG _ _ a HGst) Hw))).
    pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs1 _ G2_KEPT4 HS HAE
                  ltac:(vm_compute; reflexivity)) as KR3.
    cbn [ms_regs restrict] in KR3.
    g2_reg HS (12%bv : bv 5) M12.
    pmkst HS.
    apply (HK _ _ _ AF_gn_rig ltac:(right; split; [reflexivity | lia]) HJ
             ltac:(intros r Hr; rewrite (KR3 r Hr); exact (KR1 r Hr))); [| exact MV | exact KEEP | exact WK].
    rewrite M12. g2_U. rewrite ?ew_ewset_other by lia.
    rewrite (U_atom Eb 12 _ E12) by lia. unfold w64. rewrite unsigned_lit_small by lia. lia.
Qed.
(* ------------------------------------------------------------------ the frame across the store.
   The written cell is one of reads[0..3], inside [F + 192, F + 208): above every cell of the frame the
   arm keeps (the deepest is F + 184, eight bytes), and far above the fake frame and its shadow, which
   lie below alloc_ceiling < F. *)
Lemma g2_gframe_kept : forall cx FF (W : world segs) mem mem' (cell : Z),
  gframe cx fake_shadow_open FF W mem ->
  alloc_ceiling + 128 <= lf_F cx -> lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) <= 2 ^ 47 ->
  4096 <= FF -> FF + 128 <= alloc_ceiling ->
  lf_F cx + 192 <= cell -> cell + 4 <= lf_F cx + 208 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (cell <= a < cell + 4) -> abyte_kept W mem W mem' a) ->
  (forall a, writable_at segs (arm W mem) a -> writable_at segs (arm W mem') a) ->
  gframe cx fake_shadow_open FF W mem'.
Proof.
  intros cx FF W mem mem' cell HFR HFlo HFhi Hsp HFF0 HFF1 Hc1 Hc2 KEEP WK.
  pose proof YM05.alloc_ceiling_value as AC.
  destruct HFR as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 &
                   A17 & A18 & A19 & A20 & A21 & A22 & A23 & A24).
  assert (HSB : SB = 2147450880) by reflexivity.
  assert (KV : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 -> (a + 8 <= cell \/ cell + 4 <= a) ->
      sv8 W mem a v -> sv8 W mem' a v)
    by (intros a v H0 H1 H2 Hv; apply (gk_sv8_kept W W mem mem' a v);
        [intros x Hx; apply KEEP; lia | exact Hv]).
  assert (KW : forall a n, awr W mem a n -> awr W mem' a n)
    by (intros a n Hw i Hi; apply WK; exact (Hw i Hi)).
  assert (HFFs : 0 <= SB + FF / 8 /\ SB + FF / 8 + 16 <= alloc_ceiling).
  { pose proof (Z.div_pos FF 8 ltac:(lia) ltac:(lia)) as Hd1.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd2.
    unfold SB in *. lia. }
  split.
  { intros o r Hin.
    assert (Ho : 8 <= o <= 104).
    { cbn in Hin. repeat (destruct Hin as [Eo | Hin]; [inversion Eo; lia|]). destruct Hin. }
    apply KV; [lia | lia | right; lia | exact (A1 o r Hin)]. }
  split; [exact (KW _ _ A2)|].
  split; [apply KV; [lia | lia | left; lia | exact A3]|].
  split; [apply KV; [lia | lia | left; lia | exact A4]|].
  split; [apply KV; [lia | lia | left; lia | exact A5]|].
  split; [apply KV; [lia | lia | left; lia | exact A6]|].
  split; [apply KV; [lia | lia | left; lia | exact A7]|].
  split; [apply KV; [lia | lia | left; lia | exact A8]|].
  split; [apply KV; [lia | lia | left; lia | exact A9]|].
  split; [apply KV; [lia | lia | left; lia | exact A10]|].
  split; [apply KV; [lia | lia | left; lia | exact A11]|].
  split; [apply KV; [lia | lia | left; lia | exact A12]|].
  split; [apply KV; [lia | lia | left; lia | exact A13]|].
  split; [apply KV; [lia | lia | left; lia | exact A14]|].
  split; [apply KV; [lia | lia | left; lia | exact A15]|].
  split; [apply KV; [lia | lia | left; lia | exact A16]|].
  split; [apply KV; [lia | lia | left; lia | exact A17]|].
  split; [apply KV; [lia | lia | left; lia | exact A18]|].
  split; [apply KV; [lia | lia | left; lia | exact A19]|].
  split; [apply KV; [lia | lia | left; lia | exact A20]|].
  split; [apply KV; [lia | lia | left; lia | exact A21]|].
  split; [exact (KW _ _ A22)|].
  split; [|exact (KW _ _ A24)].
  apply (akept_garr8 W mem); [|exact A23].
  intros x Hx. unfold fake_shadow_open in Hx. cbn [length] in Hx. apply KEEP; lia.
Qed.

(* ------------------------------------------------------------------ the model value of reads[k] *)
Lemma g2_reads_val : forall m (q : nat),
  (if g2_sopen (nth q (lm_hs m) None) =? 0 then 0
   else g2_srcv (lm_es m) (g2_sfd (nth q (lm_hs m) None))) = gn_reads m q.
Proof.
  intros m q. unfold gn_reads, g2_srcv, g2_sopen, g2_sfd, gn_src.
  destruct (nth q (lm_hs m) None) as [h|]; reflexivity.
Qed.
Lemma g2_reads_rng : forall m (q : nat), 0 <= gn_reads m q <= 1.
Proof.
  intros m q. unfold gn_reads. destruct (nth q (lm_hs m) None) as [h|]; [|lia].
  destruct (gn_src m (hs_fd h)) as [i|]; [|lia].
  destruct (re_eof (nth i (lm_es m) gn_e0) =? 0); lia.
Qed.

(* ------------------------------------------------------------------ one trip of the reads[] loop *)
Lemma g2_step : forall (q : nat) cx t m W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  GL1 B G_fr fr_FP LS RINV cx t m q W c ->
  SRr segs W c (fun W' c' => GL1 B G_fr fr_FP LS RINV cx t m (S q) W' c' \/
                             GRG B G_fr fr_FP LS RINV cx t m W' c').
Proof.
  intros q cx t m W c HB HL1.
  destruct HL1 as (regs & mem & md & ly & St & kk & fpos & Hc & HGST & HLS & HRI & HOP & HKR &
                   R20 & R21 & R12 & R5 & R6 & Hq & HCELLS & HAWR & HAT & HPRE).
  destruct HGST as (HCOM & HMOD & HSEP).
  destruct HCOM as (HJ & HFRM & HP40 & HN144 & HIN & HROM & HJT & HFL).
  pose proof HKR as (K2 & K8 & K9 & K18 & K19 & K23 & K24 & K25 & K26 & K3 & K4 & K27).
  destruct (gn_nums B MT XM_LIB RLO RHI fr_live_pre G_fr fr_FP LAWS cx [(1, fpos)] ly St W mem md kk fpos
              HB HJ eq_refl) as (Hal & Hsp & HF32 & HFb & HFF0 & HFF1 & HFFapp & Hfrs & HAR).
  cbv zeta in Hsp, HF32, HFb, HFF0, HFF1.
  pose proof YM05.alloc_ceiling_value as AC. unfold LLVMF_STK in Hsp.
  pose proof HB as (HAI & HPRE2). pose proof HPRE2 as (_ & _ & _ & _ & _ & Hnlen & _).
  pose proof HMOD as (Hlen4 & HSL & HREL & _).
  pose proof HREL as (Msrc & _ & Mnsrc & _ & _ & _ & Hle16 & HGin & (tail & HTAB) & _ & _).
  destruct (g2_pads_of_relay ly St W mem (lm_G m) (lm_es m) HREL) as (HPAD & HFDS & HEOF).
  pose proof (HSL q ltac:(lia)) as HSLOT.
  destruct (g2_slot_at ly St W mem q (nth q (lm_hs m) None) HSLOT) as (Mfd & Mopen & Hfdr & Hopr).
  assert (HRS : rg_s fr_RG = 6129888) by reflexivity.
  assert (HAS : ASRC = 96) by reflexivity.
  set (A := rg_s fr_RG + ASRC * Z.of_nat q) in *.
  assert (HA32 : A mod 32 = 0)
    by (unfold A; rewrite HRS, HAS;
        replace (6129888 + 96 * Z.of_nat q) with ((191559 + 3 * Z.of_nat q) * 32) by lia;
        apply Z_mod_mult).
  assert (HZSA : azs B A ASRC)
    by (apply (g2_azs_sub (rg_s fr_RG) (4 * ASRC)); [exact HZS | unfold A; lia | unfold A; lia]).
  assert (HW192 : forall a, lf_F cx + 192 <= a < lf_F cx + 208 -> writable_at segs (arm W mem) a).
  { intros a Ha. replace a with (lf_F cx + 192 + (a - (lf_F cx + 192))) by lia. apply HAWR. lia. }
  rewrite Hc. unfold cfg_at.
  change (w64 (fr_B0 + AF_gn_l1)) with (Z_to_bv 64 (BASE + AF_gn_l1)).
  (* 0x84738 -> 0x8474c *)
  eapply (g2_run1 W regs mem md q LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
            (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly St kk _ Hq R12 R20 K26 HJ).
  intros regs1 md1 HJ1 KR1 R11a R10a.
  (* 0x8474c -> 0x847ec *)
  eapply (g2_run2 W regs1 mem md1 A (g2_sfd (nth q (lm_hs m) None)) (g2_sopen (nth q (lm_hs m) None))
            (lm_G m) (lm_es m) tail LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
            (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly St kk _
            HJ1 HGin HTAB HPAD HFDS HEOF Hle16 Mnsrc Msrc HZSA Mfd Hfdr Mopen Hopr
            ltac:(unfold A; lia) ltac:(unfold A; rewrite HAS; lia) HA32
            R11a R10a
            ltac:(rewrite (KR1 18%bv ltac:(cbv; tauto)); exact K18)
            ltac:(rewrite (KR1 23%bv ltac:(cbv; tauto)); exact K23)
            ltac:(rewrite (KR1 26%bv ltac:(cbv; tauto)); exact K26)).
  intros regs2 md2 HJ2 KR2 R18b R23b R10b.
  rewrite g2_reads_val in R10b.
  (* 0x847ec -> 0x84738 / 0x84834 *)
  eapply (g2_run3 W regs2 mem md2 (lf_F cx) (gn_reads m q) q LLVMF_STK (spZ (c_regs cx))
            (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly St kk _
            HJ2 Hq ltac:(lia) ltac:(lia) HF32 (g2_reads_rng m q) ltac:(unfold LLVMF_STK; lia) ltac:(lia)
            HW192 R10b
            ltac:(rewrite (KR2 12%bv ltac:(cbv; tauto)), (KR1 12%bv ltac:(cbv; tauto)); exact R12)
            ltac:(rewrite (KR2 5%bv ltac:(cbv; tauto)), (KR1 5%bv ltac:(cbv; tauto)); exact R5)
            ltac:(rewrite (KR2 6%bv ltac:(cbv; tauto)), (KR1 6%bv ltac:(cbv; tauto)); exact R6)
            ltac:(rewrite (KR2 26%bv ltac:(cbv; tauto)), (KR1 26%bv ltac:(cbv; tauto)); exact K26)).
  intros regs3 mem3 md3 pc Hpc HJ3 KR3 R12c MV KEEP WK.
  (* ---- what the store kept ---- *)
  assert (KEEPL : forall a, 0 <= a < GK_CEIL8 -> abyte_kept W mem W mem3 a).
  { intros a Ha. apply KEEP; [unfold GK_CEIL8 in *; lia | unfold GK_CEIL8 in *; lia]. }
  assert (HMOD3 : amodel_at B ly St W mem3 m)
    by (apply (gk_amodel_kept B LAWS ly St W mem md W mem3 m HAR HMOD (proj1 HERRNO)
                 ltac:(unfold GK_CEIL8; exact (proj2 HERRNO)) KEEPL)).
  assert (HIN3 : ainput_at B cx ly St W mem3)
    by (apply (gk_ainput_kept B LAWS cx ly St W mem md W mem3 HAR HIN (eq_sym Hnlen) KEEPL)).
  assert (HROM3 : rom_view segs W mem3) by (apply (gk_rom_kept W W mem mem3 HROM KEEPL)).
  assert (HJT3 : jt_rom W mem3) by (apply (gk_jt_kept W W mem mem3 HJT KEEPL)).
  assert (HFRM3 : gframe cx fake_shadow_open (frame_addr ly 1 fpos) W mem3)
    by (apply (g2_gframe_kept cx (frame_addr ly 1 fpos) W mem mem3
                 (lf_F cx + 192 + 4 * Z.of_nat q) HFRM ltac:(unfold LLVMF_STK in *; lia)
                 ltac:(lia) ltac:(lia) HFF0 HFF1 ltac:(lia) ltac:(lia) KEEP WK)).
  assert (KV8 : forall a v, 0 <= a -> a + 8 <= 2 ^ 64 ->
      (a + 8 <= lf_F cx + 192 + 4 * Z.of_nat q \/ lf_F cx + 192 + 4 * Z.of_nat q + 4 <= a) ->
      sv8 W mem a v -> sv8 W mem3 a v)
    by (intros a v H0 H1 H2 Hv; apply (gk_sv8_kept W W mem mem3 a v);
        [intros x Hx; apply KEEP; lia | exact Hv]).
  assert (HP40' : sv8 W mem3 (lf_F cx + 40) (c_p cx + gn_kq cx m))
    by (apply KV8; [lia | lia | left; lia | exact HP40]).
  assert (HN144' : sv8 W mem3 (lf_F cx + 144) (c_n cx - gn_kq cx m))
    by (apply KV8; [lia | lia | left; lia | exact HN144]).
  assert (HAT' : sv8 W mem3 (lf_F cx + 208) 0)
    by (apply KV8; [lia | lia | right; lia | exact HAT]).
  assert (HFL' : sv8 W mem3 (frame_addr ly 1 fpos + 120) (flag_addr ly 1 fpos))
    by (apply KV8; [lia | lia | left; lia | exact HFL]).
  assert (HAWR' : awr W mem3 (lf_F cx + 192) 16)
    by (intros i Hi; apply WK; exact (HAWR i Hi)).
  assert (CELLS : forall j, (j < S q)%nat ->
      gn_sv4 W mem3 (lf_F cx + 192 + 4 * Z.of_nat j) (gn_reads m j)).
  { intros j Hj. destruct (Nat.eq_dec j q) as [->|Hne]; [exact MV|].
    apply (akept_vm W mem); [|exact (HCELLS j ltac:(lia))].
    intros x Hx. cbn in Hx. apply KEEP; lia. }
  assert (PREF : gn_prefix_at cx m W mem3 (frame_addr ly 1 fpos)).
  { destruct HPRE as (P1 & P2 & P3 & P4 & P5).
    assert (HFFc : forall a, frame_addr ly 1 fpos + 32 <= a < frame_addr ly 1 fpos + 80 ->
        aview segs (w_H W) mem3 a = aview segs (w_H W) mem a)
      by (intros a Ha; exact (proj1 (KEEP a ltac:(lia) ltac:(lia)))).
    split; [|split; [|split; [|split]]].
    - intros i Hi. rewrite (HFFc (frame_addr ly 1 fpos + 32 + i) ltac:(lia)). exact (P1 i Hi).
    - rewrite (HFFc (frame_addr ly 1 fpos + 32 + Z.of_nat (length (gn_pre cx m))) ltac:(lia)).
      exact P2.
    - intros a Ha. rewrite (HFFc a Ha). exact (P3 a Ha).
    - exact P4.
    - exact P5. }
  assert (KREGS : gn_kregs B cx t (frame_addr ly 1 fpos) regs3).
  { split; [rewrite (KR3 2%bv ltac:(cbv; tauto)), (KR2 2%bv ltac:(cbv; tauto)),
              (KR1 2%bv ltac:(cbv; tauto)); exact K2|].
    split; [rewrite (KR3 8%bv ltac:(cbv; tauto)), (KR2 8%bv ltac:(cbv; tauto)),
              (KR1 8%bv ltac:(cbv; tauto)); exact K8|].
    split; [rewrite (KR3 9%bv ltac:(cbv; tauto)), (KR2 9%bv ltac:(cbv; tauto)),
              (KR1 9%bv ltac:(cbv; tauto)); exact K9|].
    split; [rewrite (KR3 18%bv ltac:(cbv; tauto)); exact R18b|].
    split; [rewrite (KR3 19%bv ltac:(cbv; tauto)), (KR2 19%bv ltac:(cbv; tauto)),
              (KR1 19%bv ltac:(cbv; tauto)); exact K19|].
    split; [rewrite (KR3 23%bv ltac:(cbv; tauto)); exact R23b|].
    split; [rewrite (KR3 24%bv ltac:(cbv; tauto)), (KR2 24%bv ltac:(cbv; tauto)),
              (KR1 24%bv ltac:(cbv; tauto)); exact K24|].
    split; [rewrite (KR3 25%bv ltac:(cbv; tauto)), (KR2 25%bv ltac:(cbv; tauto)),
              (KR1 25%bv ltac:(cbv; tauto)); exact K25|].
    split; [rewrite (KR3 26%bv ltac:(cbv; tauto)), (KR2 26%bv ltac:(cbv; tauto)),
              (KR1 26%bv ltac:(cbv; tauto)); exact K26|].
    split; [rewrite (KR3 3%bv ltac:(cbv; tauto)), (KR2 3%bv ltac:(cbv; tauto)),
              (KR1 3%bv ltac:(cbv; tauto)); exact K3|].
    split; [rewrite (KR3 4%bv ltac:(cbv; tauto)), (KR2 4%bv ltac:(cbv; tauto)),
              (KR1 4%bv ltac:(cbv; tauto)); exact K4|].
    rewrite (KR3 27%bv ltac:(cbv; tauto)), (KR2 27%bv ltac:(cbv; tauto)),
      (KR1 27%bv ltac:(cbv; tauto)); exact K27. }
  assert (R20c : getr regs3 20 = w64 (rg_s fr_RG))
    by (rewrite (KR3 20%bv ltac:(cbv; tauto)), (KR2 20%bv ltac:(cbv; tauto)),
          (KR1 20%bv ltac:(cbv; tauto)); exact R20).
  assert (R21c : getr regs3 21 = w64 (gn_id cx m))
    by (rewrite (KR3 21%bv ltac:(cbv; tauto)), (KR2 21%bv ltac:(cbv; tauto)),
          (KR1 21%bv ltac:(cbv; tauto)); exact R21).
  apply SRr_ret.
  destruct Hpc as [(-> & Hlt) | (-> & ->)].
  - left. exists regs3, mem3, md3, ly, St, kk, fpos.
    split; [unfold cfg_at; change (w64 (fr_B0 + AF_gn_l1)) with (Z_to_bv 64 (BASE + AF_gn_l1));
            reflexivity|].
    split; [split; [split; [exact HJ3|]; split; [exact HFRM3|]; split; [exact HP40'|];
                    split; [exact HN144'|]; split; [exact HIN3|]; split; [exact HROM3|];
                    split; [exact HJT3 | exact HFL']|];
            split; [exact HMOD3 | exact HSEP]|].
    split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|]. split; [exact KREGS|].
    split; [exact R20c|]. split; [exact R21c|].
    split; [rewrite R12c; unfold w64; f_equal; lia|].
    split; [rewrite (KR3 5%bv ltac:(cbv; tauto)), (KR2 5%bv ltac:(cbv; tauto)),
              (KR1 5%bv ltac:(cbv; tauto)); exact R5|].
    split; [rewrite (KR3 6%bv ltac:(cbv; tauto)), (KR2 6%bv ltac:(cbv; tauto)),
              (KR1 6%bv ltac:(cbv; tauto)); exact R6|].
    split; [lia|]. split; [exact CELLS|].
    split; [exact HAWR'|]. split; [exact HAT' | exact PREF].
  - right. exists regs3, mem3, md3, ly, St, kk, fpos.
    split; [unfold cfg_at; change (w64 (fr_B0 + AF_gn_rig)) with (Z_to_bv 64 (BASE + AF_gn_rig));
            reflexivity|].
    split; [split; [split; [exact HJ3|]; split; [exact HFRM3|]; split; [exact HP40'|];
                    split; [exact HN144'|]; split; [exact HIN3|]; split; [exact HROM3|];
                    split; [exact HJT3 | exact HFL']|];
            split; [exact HMOD3 | exact HSEP]|].
    split; [exact HLS|]. split; [exact HRI|]. split; [exact HOP|]. split; [exact KREGS|].
    split; [exact R20c|]. split; [exact R21c|].
    split; [intros j Hj; apply CELLS; lia|].
    split; [exact HAWR'|]. split; [exact HAT' | exact PREF].
Qed.

(* ------------------------------------------------------------------ the loop, by the trips left *)
Lemma g2_loop : forall (n q : nat) cx t m W c,
  (q + n = 4)%nat ->
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  GL1 B G_fr fr_FP LS RINV cx t m q W c ->
  SRr segs W c (GRG B G_fr fr_FP LS RINV cx t m).
Proof.
  induction n as [|n IH]; intros q cx t m W c Hn HB HL1.
  - exfalso. pose proof HL1 as (regs & mem & md & ly & S & kk & fpos & _ & _ & _ & _ & _ & _ &
      _ & _ & _ & _ & _ & Hq & _). lia.
  - eapply SRr_bind; [exact (g2_step q cx t m W c HB HL1)|].
    intros W' c' _ [HL1' | HRG]; [exact (IH (S q) cx t m W' c' ltac:(lia) HB HL1') |].
    apply SRr_ret. exact HRG.
Qed.

(* ================================================================== GP2 of
   lib/A/W_LLVMFuzzerTestOneInput_gone.v: the reads[] loop, 0x84738 -> 0x84834 *)
Lemma gp2_l1_rig : forall q cx t m W c,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx -> GL1 B G_fr fr_FP LS RINV cx t m q W c ->
  SRr segs W c (GRG B G_fr fr_FP LS RINV cx t m).
Proof.
  intros q cx t m W c HB HL1.
  pose proof HL1 as (regs & mem & md & ly & S & kk & fpos & _ & _ & _ & _ & _ & _ &
    _ & _ & _ & _ & _ & Hq & _).
  exact (g2_loop (4 - q)%nat q cx t m W c ltac:(lia) HB HL1).
Qed.

End gp2.
