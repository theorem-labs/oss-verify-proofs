(* pcap_source_next (0x8181c) on the ASan build of libreac v1.9.0: the skip phase, the walk of
   0x81ac0 .. 0x81afc (the cut pcs NP_sk1, NP_sk0, NP_sk_ra of PcapSourceNextDefs.v; the cut
   NP_skc = 0x81ad8 is this file's own).

   The record at q is longer than the caller's buffer (cap < incl). The phase starts at NP_sk1 with
   the predicate nx_sk1_inv of PcapSourceNextSkipDefs.v and ends in one of three later phases:
   - cap = 0 (`beqz s7` 0x81ac0, a KBig0 record): the exit join NP_exit 0x81d24, result -1, the stream
     at q + 16 (nx_sk1_step);
   - cap <> 0: the skip loop 0x81ac4 .. 0x81afc reads the record in chunks of nk = min (cap, rest)
     bytes into the caller's buffer (`fread(buf, 1, nk, f)` 0x81af0). nxs_head walks 0x81ac4 .. 0x81ad4
     (the chunk into s11) to NP_skc; nxs_tail walks NP_skc .. 0x81afc: the shadow check of ps, the
     fread (afread_spec), then a short read (`bne a0,s11` 0x81af4, a KCutBig record) goes to the
     exit join with result -1 and the stream at |C|; else s9 -= nk, and `bnez s9` (0x81afc) goes back
     to NP_sk0 with the rest r - nk, or, when the rest is 0 (a KBig record), to NP_empty 0x81b00 with
     the stream at q + 16 + incl, where PcapSourceNextEmpty.v's nx_empty_step takes the run to NP_loop.
   pb_skip is the phase lemma; the skip loop is proved by induction on the bytes of the record still
   to read (nx_sk0_inv).

   Every number is read from the pinned fuzz_pcap.asan image
   (sha256 b7a91d9b1fb0017d...), disassembly next.dis (sha256 06286410ee55; internal record). *)
(* Modified by Theorem Labs, 2026-10: the uses of PcapSourceNextSkipDefs.v's nxs_vm_frame and nxs_ra_frame (deleted)
   name lib/A/Prog/PcapSourceCloseSpec.v's vm_frame_segs and ra_frame. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q YA03.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import YI16 YE00 YE01 YC5d YM05.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaTable PaSym PaShadow.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Reusable Require Import PaRun.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PaJournal PcapSyms PcapList PcapAddr PcapPa PcapPaLib PcapBase.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Stdio Require Import PSource PSourceMeta PFreadM PFreadISpec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextSeat PcapSourceNextKit PcapSourceClose PcapSourceNextEmpty.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require YC4b.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require Import PcapSourceNextDefs PcapSourceNextSkipDefs.
(* The image-free frame lemmas vm_frame_segs and ra_frame, Required without Import and used qualified. *)
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.A.Prog Require PcapSourceCloseSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

(* ---------------------------------------------------------------------------------------------- *)
(* The model's oversize records                                                                     *)
(* ---------------------------------------------------------------------------------------------- *)

Lemma nxs_incl_range : forall sw F q, 0 <= PSN.incl sw F q < 2 ^ 32.
Proof.
intros sw F q. unfold PSN.incl, PSN.hw, PSN.w32le, PSN.fb.
assert (R : forall (b : byte), 0 <= bv_unsigned b < 256)
  by (intros b; pose proof (bv_unsigned_in_range 8 b) as Hb; change (bv_modulus 8) with 256 in Hb; exact Hb).
destruct sw; repeat match goal with |- context [bv_unsigned ?x] =>
  lazymatch goal with H : 0 <= bv_unsigned x < 256 |- _ => fail | _ => pose proof (R x) end end; lia.
Qed.

(* A record longer than the buffer is one of three kinds. *)
Lemma nxs_kind_big : forall sw F cap q,
  16 <= PSN.flen F - q -> PSN.incl sw F q <> 0 -> cap < PSN.incl sw F q ->
  (cap = 0 /\ PSN.kind sw F cap q = PSN.KBig0) \/
  (cap <> 0 /\ q + 16 + PSN.incl sw F q <= PSN.flen F /\ PSN.kind sw F cap q = PSN.KBig) \/
  (cap <> 0 /\ PSN.flen F < q + 16 + PSN.incl sw F q /\ PSN.kind sw F cap q = PSN.KCutBig).
Proof.
intros sw F cap q H16 Hnz Hcap. unfold PSN.kind.
destruct (Z.eqb_spec (PSN.flen F - q) 0); [lia|].
destruct (Z.ltb_spec (PSN.flen F - q) 16); [lia|].
destruct (Z.eqb_spec (PSN.incl sw F q) 0); [lia|].
destruct (Z.leb_spec (PSN.incl sw F q) cap); [lia|].
destruct (Z.eqb_spec cap 0); [left; split; [assumption | reflexivity]|].
destruct (Z.leb_spec (q + 16 + PSN.incl sw F q) (PSN.flen F)).
- right; left. auto.
- right; right. auto.
Qed.


(* The model's end of the call when the record at q ends it (KBig0, KCutBig). *)
Lemma nxs_exit_model : forall sw C cap p q lh lol lvt lvid tsv,
  nx_chain_inv sw (nxF C) cap p q lh -> q <= Z.of_nat (length C) ->
  PSN.kind sw (nxF C) cap q = PSN.KBig0 \/ PSN.kind sw (nxF C) cap q = PSN.KCutBig ->
  nx_res sw C cap p = -1 /\ nx_pos sw C cap p = PSN.pos_of sw (nxF C) cap q /\
  nx_orig sw C cap p lol = PSN.orig sw (nxF C) q /\ nx_fit sw C cap p = false /\
  nx_vtag sw C cap p lvt = lvt /\ nx_vid sw C cap p lvid = lvid /\ nx_tsv sw C cap p tsv = tsv.
Proof.
intros sw C cap p q lh lol lvt lvid tsv HI Hq HK.
assert (Hq' : q <= Z.of_nat (length (nxF C))) by (rewrite nxF_length; exact Hq).
assert (K1 : PSN.kind sw (nxF C) cap q <> PSN.KEmpty) by (destruct HK as [K|K]; rewrite K; discriminate).
assert (K2 : PSN.kind sw (nxF C) cap q <> PSN.KBig) by (destruct HK as [K|K]; rewrite K; discriminate).
destruct (nx_chain_stop _ _ _ _ _ _ HI Hq' K1 K2) as [EQ ELH].
assert (ELH' : PSN.psn_lh sw (nxF C) cap p = Some q) by (rewrite ELH; destruct HK as [K|K]; rewrite K; reflexivity).
assert (EK : nx_kind sw C cap p = PSN.kind sw (nxF C) cap q) by (unfold nx_kind, nx_q; rewrite EQ; reflexivity).
assert (EF : nx_fit sw C cap p = false) by (unfold nx_fit; rewrite EK; destruct HK as [K|K]; rewrite K; reflexivity).
unfold nx_res, nx_pos, nx_orig, nx_vtag, nx_vid, nx_tsv, nx_lh, nx_q. rewrite EQ, ELH'. rewrite EF.
unfold nx_fit in EF.
split; [unfold PSN.res_of; destruct HK as [K|K]; rewrite K; reflexivity|].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; reflexivity.
Qed.

(* The model's side of one turn of the skip loop: r bytes of the record at q still to read, the
   stream at p = q + 16 + incl - r, the chunk nk = min (cap, r), the fread's count j = min (nk, |C| - p). *)
Lemma nxs_turn_model : forall sw C cap q r nk p,
  q + 16 <= Z.of_nat (length C) -> PSN.incl sw (nxF C) q <> 0 -> cap < PSN.incl sw (nxF C) q ->
  0 < r <= PSN.incl sw (nxF C) q -> cap <> 0 -> 0 <= cap -> nk = Z.min cap r ->
  p = q + 16 + PSN.incl sw (nxF C) q - r -> p <= Z.of_nat (length C) ->
  (Z.min nk (Z.of_nat (length C) - p) <> nk ->
     PSN.kind sw (nxF C) cap q = PSN.KCutBig /\ p + Z.min nk (Z.of_nat (length C) - p) = Z.of_nat (length C)) /\
  (Z.min nk (Z.of_nat (length C) - p) = nk -> nk = r -> PSN.kind sw (nxF C) cap q = PSN.KBig) /\
  0 <= Z.min nk (Z.of_nat (length C) - p) <= nk.
Proof.
intros sw C cap q r nk p Hq16 Hinz Hcap Hr Hc0 Hcap0 Hnk Hp HpC.
assert (HlF : 16 <= PSN.flen (nxF C) - q) by (unfold PSN.flen; rewrite nxF_length; lia).
destruct (nxs_kind_big sw (nxF C) cap q HlF Hinz Hcap) as [(C0 & _) | [(_ & Hle & HK) | (_ & Hgt & HK)]];
  [exfalso; exact (Hc0 C0) | |]; unfold PSN.flen in *; rewrite nxF_length in *;
  pose proof (Z.min_spec cap r) as M1; pose proof (Z.min_spec nk (Z.of_nat (length C) - p)) as M2;
  set (I := PSN.incl sw (nxF C) q) in *; set (m := Z.min nk (Z.of_nat (length C) - p)) in *;
  set (L := Z.of_nat (length C)) in *.
- split; [intros Hj; exfalso; apply Hj; lia|]. split; [intros _ _; exact HK|]. lia.
- split; [intros Hj; split; [exact HK | lia]|]. split; [intros Hj Hr'; exfalso; lia|]. lia.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg pcap_listing}.
#[local] Abbreviation SEGS := (pa_segs).
#[local] Abbreviation BASE := (pa_val A_TEXT).
#[local] Abbreviation VAL := (pa_val).
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

Section c.
Variable B : asyms.
Variable MT : ameter_ops.
Variable KS : asource_syms.
Hypothesis LAWS : AR_laws SEGS B.

(* ---- a cut's machine state with only its pc changed (a branch that only moves the pc) ---- *)

Lemma nxs_ms_eta : forall cx fp pc W3 ms3 sh, nx_body0 cx fp pc W3 ms3 sh ->
  ms3 = mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc)) (ms_mem ms3) (seg_rom SEGS).
Proof.
intros cx fp pc W3 ms3 sh HB. unfold nx_body0 in HB.
destruct HB as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfc & _).
destruct ms3 as [regs0 fregs0 pcv0 pend0 resv0 fcsr0 mem0 rom0].
cbn [ms_pc_val ms_resv ms_svc_pending ms_rom ms_fregs ms_fcsr ms_regs ms_mem] in *.
subst. reflexivity.
Qed.

Lemma nxs_body_pc : forall cx fp pc pc' W3 ms3 sh, nx_body cx fp pc W3 ms3 sh ->
  nx_body cx fp pc' W3 (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc')) (ms_mem ms3) (seg_rom SEGS)) sh.
Proof.
intros cx fp pc pc' W3 ms3 sh [HB0 Hsl]. unfold nx_body, nx_body0 in *.
destruct HB0 as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfc & Hregs & Hsaved & Hhdr & Hflag & Hsh & Hlen & H18 & H19 & HF0).
split; [|exact Hsl].
split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
split; [reflexivity|]. split; [reflexivity|].
split; [exact Hregs|]. split; [exact Hsaved|]. split; [exact Hhdr|]. split; [exact Hflag|].
split; [exact Hsh|]. split; [exact Hlen|]. split; [exact H18|]. split; [exact H19 | exact HF0].
Qed.

Lemma nxs_mid_pc : forall cx fp pc pc' sh E q ol vt vid tv k2 ly3 S3 W3 ms3 md3 md3',
  nx_mid B MT KS cx fp pc sh E q ol vt vid tv k2 ly3 S3 W3 ms3 md3 ->
  m_fds md3' = m_fds md3 -> m_fs md3' = m_fs md3 ->
  nx_mid B MT KS cx fp pc' sh E q ol vt vid tv k2 ly3 S3 W3
    (mkst (ms_regs ms3) (Z_to_bv 64 (BASE + pc')) (ms_mem ms3) (seg_rom SEGS)) md3'.
Proof.
intros cx fp pc pc' sh E q ol vt vid tv k2 ly3 S3 W3 ms3 md3 md3' HM Hfd Hfs.
destruct HM as (HBD & H24 & (Hk & Hab & Hmo & Hfd0 & Hfs0) & REST).
split; [exact (nxs_body_pc cx fp pc pc' W3 ms3 sh HBD)|].
split; [exact H24|].
split; [split; [exact Hk|]; split; [exact Hab|]; split; [exact Hmo|]; split; [rewrite Hfd; exact Hfd0 | rewrite Hfs; exact Hfs0]|].
exact REST.
Qed.

(* ---- NP_sk1 (0x81ac0): `beqz s7` ---- *)

Lemma nxs_fetch_sk1 : fetch_word SEGS (Z_to_bv 64 (BASE + NP_sk1)) = Some (Z_to_bv 32 0x260b8263).
Proof. apply pa_fetch_pw. vm_compute. reflexivity. Qed.
Lemma nxs_dec_sk1 : decode_any (Z_to_bv 32 0x260b8263) = Some (Branch BC_EQ (23%bv : bv 5) (0%bv : bv 5) (0x264%bv : bv 13), 4%Z).
Proof. lazymatch goal with |- ?G => apply (@bool_decide_eq_true_1 G _); vm_cast_no_check (@eq_refl bool true) end. Qed.
Lemma nxs_ecall_sk1 : is_ecall (Z_to_bv 32 0x260b8263) = false.
Proof. vm_compute. reflexivity. Qed.

(* nx_exit_inv from the middle state at NP_exit, for a record that ends the call with -1. *)
Lemma nxs_exit_of_mid : forall cx fp q Q k2 ly3 S3 W3 ms3 md3,
  nx_mid B MT KS cx fp NP_exit NSH_ph (nx_E cx) Q (nx_ol cx (Some q)) (n_lvt cx) (n_lvid cx) (n_tsv cx)
    k2 ly3 S3 W3 ms3 md3 ->
  getr (ms_regs ms3) 22 = w64 (-1) ->
  nx_res (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = -1 ->
  nx_pos (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = Q ->
  nx_orig (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lol cx) = nx_ol cx (Some q) ->
  nx_fit (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) = false ->
  nx_vtag (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lvt cx) = n_lvt cx ->
  nx_vid (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_lvid cx) = n_lvid cx ->
  nx_tsv (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) (n_tsv cx) = n_tsv cx ->
  nx_exit_inv B MT KS cx fp k2 ly3 S3 W3 ms3 md3.
Proof.
intros cx fp q Q k2 ly3 S3 W3 ms3 md3 HM R22 Eres Epos Eorig Efit Evt Evid Ets.
destruct HM as (HBD & H24 & HJB & HK & HE & Hh & Hps & Hra & Hsrc & Hq & Hbuf & Hts).
split; [exact HBD|]. split; [exact HJB|].
unfold nx_fin_at, nx_fin. right.
split; [exact Hh|].
split; [rewrite R22, Eres; reflexivity|].
split; [exact HK|].
split; [rewrite Epos; exact Hsrc|].
split; [rewrite Eorig, Evt, Evid; exact Hps|].
split; [destruct Hbuf as (bj' & Hg & Hl); exists bj'; split; [exact Hg|]; split; [exact Hl|]; rewrite Efit; discriminate|].
intros Hts0. rewrite Ets. exact (proj1 (Hts Hts0)).
Qed.

#[local] Notation POST := (nx_post SK B MT KS).
#[local] Notation FROM := (nx_from SK B KS POST).

Lemma nxs_bt_eq0 : forall regs (r : bv 5) v, getr regs r = w64 v -> 0 <= v < 2 ^ 64 ->
  branch_taken BC_EQ (getr regs r) (getr regs (0%bv : bv 5)) = (v =? 0).
Proof.
intros regs r v Hr Hv. change (getr regs (0%bv : bv 5)) with (Z_to_bv 64 0).
change (branch_taken BC_EQ (getr regs r) (Z_to_bv 64 0)) with (bv_unsigned (getr regs r) =? bv_unsigned (Z_to_bv 64 0)).
rewrite Hr. unfold w64. rewrite !unsigned_lit_small by lia. reflexivity.
Qed.

Lemma nxs_U_add0 : forall E e, U E (SAlu ALU_ADD e (SLit 0)) = U E e.
Proof.
intros E e. rewrite U_SAlu, U_SLit. cbn [zalu_raw]. change (zcanon 0) with 0. rewrite Z.add_0_r.
apply zcanon_id. unfold U. pose proof (bv_unsigned_in_range 64 (sv_denot E e)) as Hr.
change (bv_modulus 64) with (2 ^ 64) in Hr. unfold M64. lia.
Qed.

Lemma nxs_U_subw_lo : forall E a b, U E (SAluw ALU_SUB a b) mod 2 ^ 32 = (U E a - U E b) mod 2 ^ 32.
Proof.
intros E a b. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ (Z.of_N 32 - 1)) with (2 ^ 31).
Z.div_mod_to_equations. lia.
Qed.

Lemma nxs_U_subw_zero : forall E a b, (U E a - U E b) mod 2 ^ 32 = 0 -> U E (SAluw ALU_SUB a b) = 0.
Proof.
intros E a b H. rewrite U_of_S, S_SAluw. cbn [zalu_raw].
pose proof (U_range E a) as Ra. pose proof (U_range E b) as Rb.
unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
change (2 ^ Z.of_N 64) with (2 ^ 64). change (2 ^ Z.of_N 32) with (2 ^ 32). change (2 ^ (Z.of_N 32 - 1)) with (2 ^ 31).
Z.div_mod_to_equations. lia.
Qed.

Lemma nx_sk1_step : forall R : ncx -> Z -> Prop,
  FROM (fun cx fp k2 ly3 S3 W3 ms3 md3 => exists r, nx_sk0_inv B MT KS R r cx fp k2 ly3 S3 W3 ms3 md3) ->
  FROM (nx_exit_inv B MT KS) ->
  FROM (nx_sk1_inv B MT KS R).
Proof.
intros R HSK0 HEX cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF HI.
destruct HI as (q & lh & Hnext & Hch & Hq16 & Hinz & Hcap & HM & R20 & R21 & R22 & R23 & R25 & R26).
pose proof HM as (HBD & _).
pose proof pa_B_ok as (HB0 & HB1 & _).
assert (Hcap0 : 0 <= n_cap cx <= NX_CAP_MAX).
{ destruct HM as (_ & _ & _ & _ & _ & Hh & _). pose proof HB as HB'. unfold nx_base in HB'.
  decompose [and] HB'. match goal with H : n_h cx <> 0 -> In (n_buf cx, _) _ /\ _ |- _ =>
    destruct (H Hh) as (_ & _ & _ & _ & _ & Hc & _) end. exact Hc. }
assert (HlF : 16 <= PSN.flen (nxF (n_C cx)) - q) by (unfold PSN.flen; rewrite nxF_length; lia).
rewrite (nxs_ms_eta cx fp NP_sk1 W3 ms3 NSH_ph (proj1 HBD)).
assert (BT : branch_taken BC_EQ (getr (ms_regs ms3) (23%bv : bv 5)) (getr (ms_regs ms3) (0%bv : bv 5)) = (n_cap cx =? 0))
  by (apply nxs_bt_eq0; [exact R23 | unfold NX_CAP_MAX in Hcap0; lia]).
destruct (Z.eq_dec (n_cap cx) 0) as [C0|C0].
- (* cap = 0, KBig0: the branch is taken, to NP_exit 0x81d24 *)
  destruct (nxs_kind_big (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q HlF Hinz Hcap)
    as [(_ & HK) | [(C1 & _) | (C1 & _)]]; [| exfalso; exact (C1 C0) | exfalso; exact (C1 C0)].
  eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
  + rewrite restrict_mkst_fx. eapply step_branch_tk_gen; [exact nxs_fetch_sk1 | exact nxs_ecall_sk1 | exact nxs_dec_sk1 |].
    rewrite BT, C0. reflexivity.
  + intros md' Hsame. rewrite unrestrict_mkst_mrestrict.
    replace (btgt (Z_to_bv 64 (BASE + NP_sk1)) (bv_signed (0x264%bv : bv 13))) with (Z_to_bv 64 (BASE + NP_exit))
      by (unfold btgt; rewrite YCbn.v_addi_lit; f_equal; change (bv_signed (0x264%bv : bv 13)) with 0x264;
          unfold NP_sk1, NP_exit; lia).
    apply (HEX cx fp k2 ly3 S3 W3 _ md' HB).
    * cbn [ms_mem mkst]. rewrite Hsame. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
    * exact HF.
    * assert (HKB : PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KBig0 \/
                    PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KCutBig) by (left; exact HK).
      destruct (nxs_exit_model (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) q lh (n_lol cx) (n_lvt cx) (n_lvid cx) (n_tsv cx)
        Hch ltac:(lia) HKB) as (Eres & Epos & Eorig & Efit & Evt & Evid & Ets).
      apply (nxs_exit_of_mid cx fp q (q + 16)).
      -- apply (nxs_mid_pc cx fp NP_sk1 NP_exit _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 md');
           [exact HM | rewrite Hsame; reflexivity | rewrite Hsame; reflexivity].
      -- cbn [ms_regs mkst]. exact R22.
      -- exact Eres.
      -- rewrite Epos. unfold PSN.pos_of. rewrite HK. reflexivity.
      -- exact Eorig.
      -- exact Efit.
      -- exact Evt.
      -- exact Evid.
      -- exact Ets.
- (* cap <> 0 (KBig or KCutBig): falls into the skip loop at NP_sk0 with the whole record to read *)
  eapply (SRr_step SEGS pa_wx W3); [reflexivity | |].
  + rewrite restrict_mkst_fx. eapply step_branch_ft_gen; [exact nxs_fetch_sk1 | exact nxs_ecall_sk1 | exact nxs_dec_sk1 |].
    rewrite BT. apply Z.eqb_neq. exact C0.
  + intros md' Hsame. rewrite unrestrict_mkst_mrestrict.
    replace (v_addi (Z_to_bv 64 (BASE + NP_sk1)) 4) with (Z_to_bv 64 (BASE + NP_sk0))
      by (rewrite YCbn.v_addi_lit; f_equal; unfold NP_sk1, NP_sk0; lia).
    apply (HSK0 cx fp k2 ly3 S3 W3 _ md' HB).
    * cbn [ms_mem mkst]. rewrite Hsame. apply (ajournal_materialize SEGS B LAWS pa_segs_low). exact HJ.
    * exact HF.
    * exists (nx_incl cx q). split; [exact C0|].
      exists q, lh. split; [exact Hnext|]. split; [exact Hch|]. split; [exact Hq16|].
      split; [exact Hinz|]. split; [exact Hcap|]. split; [split; [lia | lia]|].
      replace (q + 16 + nx_incl cx q - nx_incl cx q) with (q + 16) by lia.
      split; [apply (nxs_mid_pc cx fp NP_sk1 NP_sk0 _ _ _ _ _ _ _ k2 ly3 S3 W3 ms3 md3 md');
                [exact HM | rewrite Hsame; reflexivity | rewrite Hsame; reflexivity]|].
      cbn [ms_regs mkst].
      split; [exact R20|]. split; [exact R21|]. split; [exact R22|]. split; [exact R23|].
      split; [exact R25 | exact R26].
Qed.

(* The middle state's memory part across a stretch that writes only this call's own stack window
   (the spill slots): every caller byte lies below the allocator's ceiling, the window above it. *)
Lemma nxs_mid_mem_out : forall cx fp k2 ly3 S3 W3 m md3 m' q ol vt vid tv,
  nx_base SK B KS cx -> n_h cx <> 0 ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 m md3 k2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx)) ->
     aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a) ->
  (forall a, spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx) -> apresent (w_H W3) m' a) ->
  asource_img_laws SK SEGS B KS ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m (spZ (n_regs cx)) (nx_E cx) ->
  nx_ps_at SEGS (rdW W3 m) (n_ps cx) (n_h cx) (n_sw cx) ol vt vid (n_pad cx) ->
  range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (n_ps cx) PS_LEN ->
  asource_at SEGS KS (rdW W3 m) (n_h cx) (n_b cx) (n_C cx) q ->
  (exists bj', garr8 SEGS (rdW W3 m) (n_buf cx) bj' /\ length bj' = length (n_bj cx)) ->
  (n_ts cx <> 0 ->
     val_mem SEGS (rdW W3 m) (n_ts cx) 8 tv /\ range_addressable (aview SEGS (w_H W3) m) SHADOW_OFF (n_ts cx) 8) ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W3 m' (spZ (n_regs cx)) (nx_E cx) /\
  nx_ps_at SEGS (rdW W3 m') (n_ps cx) (n_h cx) (n_sw cx) ol vt vid (n_pad cx) /\
  range_addressable (aview SEGS (w_H W3) m') SHADOW_OFF (n_ps cx) PS_LEN /\
  asource_at SEGS KS (rdW W3 m') (n_h cx) (n_b cx) (n_C cx) q /\
  (exists bj', garr8 SEGS (rdW W3 m') (n_buf cx) bj' /\ length bj' = length (n_bj cx)) /\
  (n_ts cx <> 0 ->
     val_mem SEGS (rdW W3 m') (n_ts cx) 8 tv /\ range_addressable (aview SEGS (w_H W3) m') SHADOW_OFF (n_ts cx) 8).
Proof.
intros cx fp k2 ly3 S3 W3 m md3 m' q ol vt vid tv HB Hh HJ HEQ HPW ASIL (O1 & O2 & O3 & O4 & O5 & O6) Hps Hpsra Hsrc Hbuf Hts.
destruct (nx_E_below B KS LAWS cx HB Hh) as (HEb & Hspc & Hsp47).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HB as HB'. unfold nx_base in HB'.
destruct HB' as (HJ0 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _
  & Hown & Hfa1 & Hfa2 & _ & _ & _ & _ & _ & Hbufb & Htsb & Hstr & _).
pose proof HJ0 as (HAR0 & _ & _ & _ & _ & Hfrs0 & _).
unfold NX_STK, AFREAD_STK in *.
(* every byte below the ceiling is kept *)
assert (KB : forall a, 0 <= a < alloc_ceiling -> mbyte SEGS (rdW W3 m') a = mbyte SEGS (rdW W3 m) a).
{ intros a Ha. apply (mbyte_of_aview SEGS). apply HEQ; [revert Ha C1; clear; intros; lia | revert Ha Hspc; clear; intros; lia]. }
assert (KA : forall a, 0 <= a < alloc_ceiling -> aview SEGS (w_H W3) m' a = aview SEGS (w_H W3) m a).
{ intros a Ha. apply HEQ; [revert Ha C1; clear; intros; lia | revert Ha Hspc; clear; intros; lia]. }
destruct (Hstr Hh) as (Hinh & HinC & _ & HlC & _).
destruct (Hbufb Hh) as (Hinb & Hb4096 & _ & _ & Hlbj & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinh) as (_ & Hh4 & Hhc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 HinC) as (_ & HC4 & HCc & _).
destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR0 Hinb) as (_ & Hb4' & Hbc & _).
pose proof (req_size_bounds (Z.of_nat (length (n_C cx))) ltac:(lia)) as (_ & _ & HrC & _).
pose proof (req_size_bounds (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as (_ & _ & Hrb & _).
change (req_size SRC_FILE_BLOCK) with 1304 in Hhc.
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ (n_cid cx) (n_pos cx) HAR0
  ltac:(rewrite Hfrs0; apply in_or_app; left; exact Hown)) as (Hpf4 & Hpfc & _).
assert (Hps4 : 4096 <= n_ps cx) by (revert Hpf4 Hfa1; clear; intros; lia).
split.
{ split; [|split; [|split; [|split; [|split]]]].
  - intros a Ha Hw HnE. rewrite (HEQ a ltac:(revert Ha C1; clear; intros; lia) Hw). exact (O1 a Ha Hw HnE).
  - intros b mm i Hin Hi HnE. destruct (al_blocks _ _ LAWS _ _ _ _ _ b mm HAR0 Hin) as (_ & Hb4 & Hbcc & _).
    rewrite (KA (b + i) ltac:(revert Hb4 Hbcc Hi; clear; intros; lia)). exact (O2 b mm i Hin Hi HnE).
  - intros a Hi Hno Herr. pose proof (pa_segs_low a Hi) as Hlo.
    rewrite (KA a ltac:(revert Hlo C1 C5; clear; intros; lia)). exact (O3 a Hi Hno Herr).
  - intros c p a Hin Hr HnE. destruct (frames_bounds SEGS B LAWS _ _ _ _ _ c p HAR0 Hin) as (Hg4 & Hgc & Hgapp).
    pose proof (fs_frame_bytes_nonneg c) as Hnn.
    pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) c p) ltac:(revert Hg4 Hgc Hnn C1 C4; clear; intros; lia)) as Hsb1.
    pose proof (shadow_range_end (frame_addr (n_lyc cx) c p) (fs_frame_bytes c) Hnn) as Hse.
    pose proof (shadow_addr_bounds (frame_addr (n_lyc cx) c p + fs_frame_bytes c) ltac:(revert Hg4 Hgc Hnn C1 C4; clear; intros; lia)) as Hsb2.
    rewrite (KA a). { exact (O4 c p a Hin Hr HnE). }
    unfold in_zr, frame_rng in Hr. cbn [fst snd] in Hr.
    revert Hr Hg4 Hgc Hnn Hsb1 Hsb2 Hse C1 C4 C5. clear. unfold kLowMemEnd, kHighShadowEnd. intros. destruct Hr; lia.
  - intros a Ha Hw Hp. eapply (apresent_transfer SEGS); [revert Ha C1; clear; intros; lia | | |].
    + intros Him. pose proof (pa_segs_low a Him) as Hlo. revert Ha Hlo C1 C5; clear; intros; lia.
    + exact (HEQ a ltac:(revert Ha C1; clear; intros; lia) Hw).
    + exact (O5 a Ha Hw Hp).
  - exact HPW. }
split.
{ apply (nxs_ps_at_frame (rdW W3 m)); [|exact Hps]. intros x Hx. apply KB. revert Hx Hps4 Hpfc Hfa2; clear; unfold PS_LEN; intros; lia. }
split.
{ apply (PcapSourceCloseSpec.ra_frame (aview SEGS (w_H W3) m)); [exact Hpsra|]. intros x Hx. apply KA.
  revert Hx Hps4 Hpfc Hfa2 C1. clear. unfold shadow_of_addr, SHADOW_OFF, PS_LEN. intros.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia. }
split.
{ apply (asource_at_frame KS (rdW W3 m) (rdW W3 m')); [|exact Hsrc].
  intros a Ha. apply KB. destruct Ha as [Ha | [Ha | Ha]].
  - revert Ha Hh4 Hhc. unfold SRC_FILE_BLOCK. clear. intros. lia.
  - revert Ha HC4 HCc HrC. clear. intros. lia.
  - pose proof (proj1 (asil_env _ _ _ _ ASIL a Ha)) as Him. pose proof (pa_segs_low a Him) as Hlo.
    revert Hlo C1 C5. clear. intros. lia. }
split.
{ destruct Hbuf as (bj' & Hg & Hl). exists bj'. split; [|exact Hl].
  apply (garr8_frame SEGS (rdW W3 m) (rdW W3 m') _ _ Hg). intros x Hx. apply KB.
  rewrite Hl in Hx. revert Hx Hlbj Hb4' Hbc Hrb. clear. intros. lia. }
intros Hts0. destruct (Hts Hts0) as (Hv & Hra).
destruct (Htsb Hh Hts0) as (_ & _ & Ht4 & Ht47 & _ & (tc & tp & Htin & Ht1 & Ht2) & _).
destruct (frames_bounds SEGS B LAWS _ _ _ _ _ tc tp HAR0
  ltac:(rewrite Hfrs0; apply in_or_app; left; exact Htin)) as (_ & Htc & _).
split.
- apply (PcapSourceCloseSpec.vm_frame_segs _ (rdW W3 m)); [|exact Hv]. intros x Hx. apply KB. revert Hx Ht4 Htc Ht2; clear; intros; lia.
- apply (PcapSourceCloseSpec.ra_frame (aview SEGS (w_H W3) m)); [exact Hra|]. intros x Hx. apply KA.
  revert Hx Ht4 Htc Ht2 C1. clear. unfold shadow_of_addr, SHADOW_OFF. intros.
  assert (0 <= x / 8 < 2 ^ 44) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia). lia.
Qed.

(* ---- the skip loop: one turn from NP_sk0 ---- *)

Hypothesis TL : PALib B.
Hypothesis AFREAD : afread_spec SK SEGS B KS (pa_sigma PS___interceptor_trampoline_fread).
Hypothesis ASIL : asource_img_laws SK SEGS B KS.
Let RUN := paj_run B LAWS.
Let BR := paj_branch (PI := PI).

(* The symbolic registers of the turn: the seat's standard ones, with s5 = ps (atom 10, the base of
   the struct's region: `ld a3,0(s5)` 0x81ae0) and s8 = the shadow address of ps (`lbu a0,0(s8)`
   0x81ad8, which the token engine discharges from nx_SH). *)
Definition nx_sr_sk : list sv :=
  sr_set (sr_set nx_sr (21%bv : bv 5) (SOff NA_PS 0)) (24%bv : bv 5) (nx_shx (SOff NA_PS 0)).
(* The shadow span of the token runs: the whole shadow band (PcapSourceClose's CLspan). *)
Definition NXS_SPAN : Z * Z := (SHADOW_OFF, SHADOW_OFF + 2 ^ 44 - 1).
(* The atom of ps->f, the stream h. *)
Definition NA_H : nat := 562%nat.
Definition nxs_pcs : list YP09.chunk := [YP09.mkChunk PS_F_OFF (CVal 8 (SOff NA_H 0))].

Lemma nxs_regs_ok_swap : forall E sr regs (r : bv 5) e, regs_ok E sr regs -> bv_eqb r 0 = false ->
  getr regs r = sv_denot E e -> regs_ok E (sr_set sr r e) regs.
Proof.
intros E sr regs r e H Hr He r'. destruct (decide (r' = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr. exact He.
- rewrite sr_get_set_other by exact Hne. apply H.
Qed.


Lemma nxs_U_zext32 : forall E n,
  U E (SAlu ALU_SRL (SAlu ALU_SLL (SOff n 0) (SLit 32)) (SLit 32)) = bv_unsigned (ew E n) mod 2 ^ 32.
Proof.
intros E n. rewrite !U_SAlu, !U_SLit, U_SOff. cbn [zalu_raw].
change (Z.land (zcanon 32) 63) with 32. rewrite Z.add_0_r.
pose proof (bv_unsigned_in_range 64 (ew E n)) as Hr. change (bv_modulus 64) with (2 ^ 64) in Hr.
set (v := bv_unsigned (ew E n)) in *.
unfold zcanon, M64. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
rewrite (Z.mod_small v) by lia.
replace (2 ^ 64) with (2 ^ 32 * 2 ^ 32) by reflexivity.
rewrite Z.mul_mod_distr_r by lia. rewrite Z.div_mul by lia.
apply Z.mod_small. pose proof (Z.mod_pos_bound v (2 ^ 32) ltac:(lia)). lia.
Qed.

(* ---- the turn's environment, seat, geometry and landing ---- *)

Local Ltac nxs_awr U60 Hsp1 Hsp0 :=
  lazymatch goal with |- awr_ok ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok Ex rs' stk spx fp b0 bc lyx own) end;
  apply awr_ok_cons_ro; [cbn; lia|];
  eapply awr_ok_cons_stack_at; [reflexivity | exact U60 | cbn [YP09.r_wlo] | cbn [YP09.r_whi] |];
  [ revert Hsp1 Hsp0; clear; unfold NX_STK, AFREAD_STK; intros; lia
  | revert Hsp1 Hsp0; clear; unfold NX_SPILL; intros; lia
  | repeat (apply awr_ok_cons_ro; [cbn; lia|]); apply awr_ok_nil ].

(* The seat's environment at a cut: the standard one of the state's registers, with ps->f (the
   stream h) at NA_H. *)
Definition nxs_E (cx : ncx) (fp : Z) (ms3 : machine_state) : env :=
  ewset (nx_mkE cx fp (ms_regs ms3)) NA_H (w64 (n_h cx)).

Lemma nxs_env : forall cx fp ms3, nx_env cx fp (nxs_E cx fp ms3) /\ img_env VAL A_LIM (nxs_E cx fp ms3).
Proof.
intros cx fp ms3. split.
- apply nx_env_ewset; [apply nx_mkE_env | unfold NA_H; lia | unfold NA_H, NA_SP1; lia
  | unfold NA_H, NA_F; lia | unfold NA_H, NA_FL; lia | unfold NA_H, NA_FSH; lia].
- apply nx_img_env_ewset; [apply nx_mkE_img | right; unfold NA_H, A_LIM; lia].
Qed.

Lemma nxs_E_cur : forall cx fp ms3 i (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r ->
  ew (nxs_E cx fp ms3) (NA_CUR + i) = getr (ms_regs ms3) r.
Proof.
intros cx fp ms3 i r Hi Hr. unfold nxs_E. rewrite ew_ewset_other by (unfold NA_H, NA_CUR; lia).
etransitivity; [exact (nx_mkE_cur cx fp (ms_regs ms3) i Hi)|].
f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hr. unfold bv_wrap. change (bv_modulus 5) with 32.
apply Z.mod_small. lia.
Qed.

(* A register a run did not write: its value is the seat's. *)
Lemma nxs_reg_land : forall cx fp ms3 (W : world SEGS) ms ss E' i (r : bv 5), (i < 32)%nat -> Z.of_nat i = bv_unsigned r ->
  st_ok_pi SEGS VAL E' ss (restrict (w_H W) ms) -> sr_get (ss_regs ss) r = SOff (NA_CUR + i) 0 ->
  ew E' (NA_CUR + i) = ew (nxs_E cx fp ms3) (NA_CUR + i) ->
  getr (ms_regs ms) r = getr (ms_regs ms3) r.
Proof.
intros cx fp ms3 W ms ss E' i r Hi Hr HS Hsr Hag.
rewrite (st_ok_pi_restrict_reg _ E' ss ms r HS), Hsr, nx_sv_SOff0, Hag. exact (nxs_E_cur cx fp ms3 i r Hi Hr).
Qed.

Lemma nxs_geo : forall cx, nx_base SK B KS cx -> n_h cx <> 0 ->
  (spZ (n_regs cx) - 256 < n_sp1 cx <= spZ (n_regs cx) - 224) /\
  (n_sp0 cx - n_STK cx <= spZ (n_regs cx) - NX_STK /\ spZ (n_regs cx) <= n_sp0 cx) /\
  (forall a, nx_E cx a -> 4096 <= a < alloc_ceiling) /\
  alloc_ceiling + NX_STK <= spZ (n_regs cx) /\ spZ (n_regs cx) <= 2 ^ 47.
Proof.
intros cx HB Hh.
destruct (nx_E_below B KS LAWS cx HB Hh) as (HEb & Hspc & Hsp47).
split.
{ unfold n_sp1, nx_sp1, NX_MFRAME.
  pose proof (Z.mul_div_le (spZ (n_regs cx) - 224) 32 ltac:(clear; lia)) as M1.
  pose proof (Z_div_mod_eq_full (spZ (n_regs cx) - 224) 32) as M2.
  pose proof (Z.mod_pos_bound (spZ (n_regs cx) - 224) 32 ltac:(clear; lia)) as M3.
  revert M1 M2 M3. clear. intros. lia. }
split; [pose proof HB as HB'; unfold nx_base in HB'; decompose [and] HB'; split; assumption|].
split; [exact HEb|]. split; [exact Hspc | exact Hsp47].
Qed.

Lemma nxs_U60 : forall cx fp E, nx_base SK B KS cx -> n_h cx <> 0 -> nx_env cx fp E ->
  bv_unsigned (ew E NA_SP1) = n_sp1 cx.
Proof.
intros cx fp E HB Hh HE. destruct (nxs_geo cx HB Hh) as (Hsp1 & _ & _ & Hspc & Hsp47).
rewrite (proj1 (proj2 (proj2 HE))). unfold w64. apply unsigned_lit_small. pose proof asan_consts as (C1 & _).
revert Hsp1 Hspc Hsp47 C1. clear. unfold NX_STK, AFREAD_STK. intros. lia.
Qed.

Lemma nxs_SH24 : forall cx fp E, nx_base SK B KS cx -> nx_env cx fp E -> ew E NA_PS = w64 (n_ps cx) ->
  sv_denot E (nx_shx (SOff NA_PS 0)) = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)).
Proof.
intros cx fp E HB HE EPS. pose proof (nxb_ps B KS cx HB) as (Hps8 & Hps4 & Hps47 & Hpsam).
rewrite (nx_U_shx E NA_PS (n_ps cx) 0); [rewrite Z.add_0_r; reflexivity | exact (proj1 (proj2 HE)) | exact EPS
  | unfold PS_LEN in *; lia | lia | unfold PS_LEN in *; lia].
Qed.

(* The seat at a cut of the skip loop (NP_sk0, NP_skc): the struct's region holds ps->f = h, s5 is
   its base, s8 its shadow address. *)
Lemma nxs_seat : forall cx fp k2 ly3 S3 W3 ms3 md3 pc Q ol vt vid tv,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem ms3) md3 k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_mid B MT KS cx fp pc NSH_ph (nx_E cx) Q ol vt vid tv k2 ly3 S3 W3 ms3 md3 ->
  getr (ms_regs ms3) 21 = w64 (n_ps cx) ->
  ew (nxs_E cx fp ms3) NA_PS = w64 (n_ps cx) /\ ew (nxs_E cx fp ms3) NA_H = w64 (n_h cx) /\
  st_ok_pi SEGS VAL (nxs_E cx fp ms3) (nx_ss pc nx_sr_sk true NSH_ph 0 0 0 [] [nx_ps_region 0 nxs_pcs] nx_facts0)
    (restrict (w_H W3) ms3) /\
  sh_ok SEGS nx_Bx (nx_SH ++ []) (nxs_E cx fp ms3) (rdW W3 (ms_mem ms3)).
Proof.
intros cx fp k2 ly3 S3 W3 ms3 md3 pc Q ol vt vid tv HB HJ HFRM HM R21.
pose proof HM as (HBD & H24 & HJB & HK & HEn & Hh & Hps & Hpsra & Hsrc & Hq & Hbuf & Hts).
pose proof HBD as (HB0 & Hsl). pose proof HB0 as HB0'. unfold nx_body0 in HB0'.
destruct HB0' as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfc & Hregs & Hsaved & Hhdr & Hflag & Hsh & Hlen & H18 & H19 & HF0).
pose proof (nxb_ps B KS cx HB) as (Hps8 & Hps4 & Hps47 & Hpsam).
destruct (nxs_env cx fp ms3) as (HE & HEI).
set (E := nxs_E cx fp ms3) in *.
assert (HRG0 : regs_ok (nx_mkE cx fp (ms_regs ms3)) nx_sr (ms_regs ms3))
  by exact (nx_regs_ok B KS cx fp ms3 HB Hregs H18 H19).
assert (HRG1 : regs_ok E nx_sr (ms_regs ms3)).
{ apply (regs_ok_agree_p (fun n => negb (Nat.eqb n NA_H)) (nx_mkE cx fp (ms_regs ms3)) E); [| vm_compute; reflexivity | exact HRG0].
  split; [|reflexivity]. intros n Hn. unfold E, nxs_E. apply ew_ewset_other.
  intros X. subst n. rewrite Nat.eqb_refl in Hn. discriminate Hn. }
assert (EPS : ew E NA_PS = w64 (n_ps cx)).
{ pose proof HE as (AG & _). rewrite (AG NA_PS ltac:(unfold NA_PS; lia)).
  pose proof HB as HB'. unfold nx_base in HB'. decompose [and] HB'.
  match goal with HE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (n_E0 cx) n = getr (n_regs cx) r |- _ =>
    rewrite (HE0 NA_PS (10%bv : bv 5) eq_refl) end.
  match goal with H10 : getr (n_regs cx) 10 = w64 (n_ps cx) |- _ => exact H10 end. }
assert (EH : ew E NA_H = w64 (n_h cx)) by (unfold E, nxs_E; apply ew_ewset_same).
assert (Hh64 : 0 <= n_h cx < 2 ^ 64).
{ pose proof HB as HB'. unfold nx_base in HB'. decompose [and] HB'. split; assumption. }
assert (HRG : regs_ok E nx_sr_sk (ms_regs ms3)).
{ unfold nx_sr_sk. apply nxs_regs_ok_swap; [apply nxs_regs_ok_swap; [exact HRG1 | reflexivity |] | reflexivity |].
  - rewrite R21, nx_sv_SOff0, EPS. reflexivity.
  - rewrite H24. symmetry. exact (nxs_SH24 cx fp E HB HE EPS). }
assert (HPC : Forall (YP09.chunk_ok SEGS E (rdW W3 (ms_mem ms3)) (n_ps cx)) nxs_pcs).
{ constructor; [|constructor].
  apply (chunk_ok_val SEGS E _ (n_ps cx) PS_F_OFF 8 (SOff NA_H 0) (n_h cx));
    [rewrite nx_sv_SOff0, EH; reflexivity | cbn; lia | cbn; lia | exact (proj1 Hps)]. }
split; [exact EPS|]. split; [exact EH|].
split.
{ apply (nx_seat B KS LAWS TL cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFRM E pc nx_sr_sk NSH_ph 0 0 0 [] [nx_ps_region 0 nxs_pcs]
    nx_facts0 HE HEI HBD HRG); [unfold NX_FRAME; lia | constructor | lia | lia | vm_compute; reflexivity | | | |].
  - constructor; [|constructor].
    apply (nx_ps_region_ok B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFRM E 0 nxs_pcs HE); [unfold PS_LEN; lia | exact HPC].
  - cbn. repeat split.
  - apply (nx_ps_disj B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFRM E true NSH_ph 0 0 0 [] 0 nxs_pcs HE HEI);
      [unfold NX_FRAME; lia | lia | lia].
  - exact (nx_facts0_ok B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFRM E HE). }
apply (nx_shok B KS cx fp W3 ms3 HB E [] HE Hpsra); constructor.
Qed.

(* The landing: the middle state at a symbolic state's pc, from the body the seat layer gives back
   (nx_land_by), r24, the journal's bookkeeping and the memory facts. *)
Lemma nxs_land : forall cx fp k2 ly3 S3 (W : world SEGS) ms md E ss Q ol vt vid tv,
  nx_base SK B KS cx ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W (ms_mem ms) md k2 ->
  frames S3 = (NX_CID, fp) :: frames (n_Sc cx) ->
  nx_env cx fp E -> img_env VAL A_LIM E ->
  st_ok_pi SEGS VAL E ss (restrict (w_H W) ms) -> ss_resv ss = None ->
  nx_sr_ok cx fp E (ss_regs ss) -> nx_land_chk true NSH_ph (ss_mem ss) = true ->
  sv_denot E (sr_get (ss_regs ss) 24) = w64 (shadow_of_addr SHADOW_OFF (n_ps cx)) ->
  k2 = n_k cx + EV_NEXT -> ablocks B ly3 S3 = ablocks B (n_lyc cx) (n_Sc cx) -> mo_le MT (n_Sc cx) S3 0 ->
  m_fds md = m_fds (n_mdc cx) -> m_fs md = m_fs (n_mdc cx) ->
  nx_kept SEGS NX_STK B (n_lyc cx) (n_Sc cx) (n_W cx) (n_memc cx) W (ms_mem ms) (spZ (n_regs cx)) (nx_E cx) ->
  n_h cx <> 0 ->
  nx_ps_at SEGS (rdW W (ms_mem ms)) (n_ps cx) (n_h cx) (n_sw cx) ol vt vid (n_pad cx) ->
  range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (n_ps cx) PS_LEN ->
  asource_at SEGS KS (rdW W (ms_mem ms)) (n_h cx) (n_b cx) (n_C cx) Q ->
  n_p cx <= Q <= Z.of_nat (length (n_C cx)) ->
  (exists bj', garr8 SEGS (rdW W (ms_mem ms)) (n_buf cx) bj' /\ length bj' = length (n_bj cx)) ->
  (n_ts cx <> 0 -> val_mem SEGS (rdW W (ms_mem ms)) (n_ts cx) 8 tv /\
     range_addressable (aview SEGS (w_H W) (ms_mem ms)) SHADOW_OFF (n_ts cx) 8) ->
  nx_mid B MT KS cx fp (ss_pc ss) NSH_ph (nx_E cx) Q ol vt vid tv k2 ly3 S3 W ms md.
Proof.
intros cx fp k2 ly3 S3 W ms md E ss Q ol vt vid tv HB HJ HFR HE HEI HS Hrv Hsr Hchk H24 Hk2 Hab Hmo Hfd Hfs
  HK Hh Hps Hpsra Hsrc Hq Hbuf Hts.
pose proof (nx_land_by B KS LAWS cx fp k2 ly3 S3 W ms md HB HJ HFR E ss NSH_ph NSH_ph HE HEI HS Hrv Hsr Hchk
  ltac:(vm_compute; reflexivity) eq_refl Hh) as Hbd.
unfold nx_mid. split; [exact Hbd|].
split; [rewrite (st_ok_pi_restrict_reg _ E ss ms 24%bv HS); exact H24|].
split; [unfold nx_jbk; split; [exact Hk2|]; split; [exact Hab|]; split; [exact Hmo|]; split; [exact Hfd | exact Hfs]|].
split; [exact HK|]. split; [intros a Ha; exact Ha|]. split; [exact Hh|]. split; [exact Hps|].
split; [exact Hpsra|]. split; [exact Hsrc|]. split; [exact Hq|]. split; [exact Hbuf | exact Hts].
Qed.

Local Ltac nxs_reg HS r v H :=
  lazymatch type of HS with st_ok_pi _ _ ?E ?ss (restrict _ ?m) =>
    assert (H : getr (ms_regs m) r = sv_denot E v)
      by (rewrite (st_ok_pi_restrict_reg _ E ss m r HS); f_equal; vm_compute; reflexivity) end.

(* ---- the skip loop's internal cut 0x81ad8 (after the chunk is chosen: s11 = min (cap, rest)) ---- *)

Definition NP_skc : Z := NP_sk0 + 20.

Definition nx_skc_inv (R : ncx -> Z -> Prop) (r : Z)
  (cx : ncx) (fp k2 : Z) (ly3 : alayout) (S3 : astate) (W3 : world SEGS) (ms3 : machine_state)
  (md3 : Model) : Prop :=
  n_cap cx <> 0 /\ nx_skip_at B MT KS R NP_skc r cx fp k2 ly3 S3 W3 ms3 md3 /\
  getr (ms_regs ms3) 27 = w64 (Z.min (n_cap cx) r).

Let RUNTO := paj_run_to B LAWS.

(* 0x81ac4 .. 0x81ad4: a0 := the low word of s9 (the rest r), s11 := cap, and s11 := r when r <= cap
   (`bltu s7,a0` 0x81ad0). *)
Lemma nxs_head : forall (R : ncx -> Z -> Prop) r,
  FROM (nx_skc_inv R r) -> FROM (nx_sk0_inv B MT KS R r).
Proof.
intros R r HSKC cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFRM HI.
pose proof HI as (Hc0 & q & lh & Hnext & Hch & Hq16 & Hinz & Hcap & Hr & HM & R20 & R21 & R22 & R23 & R25 & R26).
pose proof HM as (HBD & H24 & HJB & HK & HEn & Hh & Hps & Hpsra & Hsrc & Hq & Hbuf & Hts).
pose proof HJB as (Hk2 & HJB_ab & Hmo & Hfd3 & Hfs3).
destruct (nxs_seat cx fp k2 ly3 S3 W3 ms3 md3 NP_sk0 _ _ _ _ _ HB HJ HFRM HM R21) as (EPS & EH & HS & SHOK).
destruct (nxs_env cx fp ms3) as (HE & HEI).
destruct (nxs_geo cx HB Hh) as (Hsp1 & Hsp0 & HEb & Hspc & Hsp47).
pose proof (nxs_U60 cx fp _ HB Hh HE) as U60.
pose proof (nxs_SH24 cx fp _ HB HE EPS) as SH24.
set (E := nxs_E cx fp ms3) in *.
assert (E23 : ew E 553%nat = w64 (n_cap cx))
  by (change 553%nat with (NA_CUR + 23)%nat; unfold E; rewrite (nxs_E_cur cx fp ms3 23 23%bv ltac:(lia) eq_refl); exact R23).
assert (E25 : bv_unsigned (ew E 555%nat) mod 2 ^ 32 = r)
  by (change 555%nat with (NA_CUR + 25)%nat; unfold E; rewrite (nxs_E_cur cx fp ms3 25 25%bv ltac:(lia) eq_refl); exact R25).
assert (Hcap0 : 0 <= n_cap cx <= NX_CAP_MAX).
{ pose proof HB as HB'. unfold nx_base in HB'. decompose [and] HB'.
  match goal with H : n_h cx <> 0 -> In (n_buf cx, _) _ /\ _ |- _ => destruct (H Hh) as (_ & _ & _ & _ & _ & Hc & _) end. exact Hc. }
pose proof HJ as HJ3.
assert (NOWR : forall a, ~ in_wrange E [nx_ps_region 0 nxs_pcs] a)
  by (intros a (rr & [<- | []] & Hrr); cbn in Hrr; lia).
(* the landing at NP_skc, the same for both arms *)
assert (LANDC : forall ss (m : machine_state) md',
  st_ok_pi SEGS VAL E ss (restrict (w_H W3) m) -> ss_resv ss = None -> ss_pc ss = NP_skc ->
  nx_sr_ok cx fp E (ss_regs ss) -> nx_land_chk true NSH_ph (ss_mem ss) = true ->
  sr_get (ss_regs ss) 24 = nx_shx (SOff NA_PS 0) ->
  sr_get (ss_regs ss) 20 = SOff (NA_CUR + 20) 0 -> sr_get (ss_regs ss) 21 = SOff NA_PS 0 ->
  sr_get (ss_regs ss) 22 = SOff (NA_CUR + 22) 0 -> sr_get (ss_regs ss) 23 = SOff (NA_CUR + 23) 0 ->
  sr_get (ss_regs ss) 25 = SOff (NA_CUR + 25) 0 -> sr_get (ss_regs ss) 26 = SOff (NA_CUR + 26) 0 ->
  getr (ms_regs m) 27 = w64 (Z.min (n_cap cx) r) ->
  ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
    ((NX_CID, fp) :: n_own cx) ly3 S3 W3 (ms_mem m) md' k2 ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx <= a < n_sp1 cx + NX_SPILL) ->
     aview SEGS (w_H W3) (ms_mem m) a = aview SEGS (w_H W3) (ms_mem ms3) a) ->
  m_fds md' = m_fds md3 -> m_fs md' = m_fs md3 ->
  SRr SEGS W3 (mkCfg m md') (nx_post SK B MT KS cx)).
{ intros ss m md' HSm Hrv Hpcm Hsr Hchk G24 G20 G21 G22 G23 G25 G26 R27 HJm HEQ Hfd Hfs.
  apply (HSKC cx fp k2 ly3 S3 W3 m md' HB HJm HFRM).
  assert (HPW : forall a, spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx) -> apresent (w_H W3) (ms_mem m) a).
  { intros a Ha. pose proof HJm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
    apply Hpres. revert Ha Hsp0; clear; intros; lia. }
  destruct (nxs_mid_mem_out cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (ms_mem m) (q + 16 + nx_incl cx q - r)
    (nx_ol cx (Some q)) (n_lvt cx) (n_lvid cx) (n_tsv cx) HB Hh HJ3
    ltac:(intros a Ha Hw; apply HEQ; [exact Ha | revert Hw Hsp1; clear; unfold NX_STK, AFREAD_STK, NX_SPILL; intros; lia])
    HPW ASIL HK Hps Hpsra Hsrc Hbuf Hts) as (HKm & Hpsm & Hpsram & Hsrcm & Hbufm & Htsm).
  split; [exact Hc0|]. split; [|exact R27].
  exists q, lh. split; [exact Hnext|]. split; [exact Hch|]. split; [exact Hq16|].
  split; [exact Hinz|]. split; [exact Hcap|]. split; [exact Hr|].
  split.
  { rewrite <- Hpcm.
    apply (nxs_land cx fp k2 ly3 S3 W3 m md' E ss _ _ _ _ _ HB HJm HFRM HE HEI HSm Hrv Hsr Hchk); try assumption.
    - rewrite G24. exact SH24.
    - rewrite Hfd. exact Hfd3.
    - rewrite Hfs. exact Hfs3. }
  split; [rewrite <- R20; exact (nxs_reg_land cx fp ms3 W3 m ss E 20 20%bv ltac:(lia) eq_refl HSm G20 eq_refl)|].
  split; [rewrite (st_ok_pi_restrict_reg _ E ss m 21%bv HSm), G21, nx_sv_SOff0; exact EPS|].
  split; [rewrite <- R22; exact (nxs_reg_land cx fp ms3 W3 m ss E 22 22%bv ltac:(lia) eq_refl HSm G22 eq_refl)|].
  split; [rewrite <- R23; exact (nxs_reg_land cx fp ms3 W3 m ss E 23 23%bv ltac:(lia) eq_refl HSm G23 eq_refl)|].
  split; [rewrite <- R25, (nxs_reg_land cx fp ms3 W3 m ss E 25 25%bv ltac:(lia) eq_refl HSm G25 eq_refl); reflexivity|].
  rewrite <- R26; exact (nxs_reg_land cx fp ms3 W3 m ss E 26 26%bv ltac:(lia) eq_refl HSm G26 eq_refl). }
paj_run_tok RUN HS HJ SHOK NXS_SPAN; [nxs_awr U60 Hsp1 Hsp0|].
rename ms into ms1, HF into HF1, HFr into HFr1, HG into HG1.
assert (EQ1 : forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx <= a < n_sp1 cx + NX_SPILL) ->
  aview SEGS (w_H W3) (ms_mem ms1) a = aview SEGS (w_H W3) (ms_mem ms3) a).
{ intros a Ha Hs. apply (nx_keep_out B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 HFRM E true NSH_ph 0 0 0 []
    [nx_ps_region 0 nxs_pcs] (ms_mem ms3) (ms_mem ms1) HE HEI HFr1 a Ha Hs); [lia | lia | exact (NOWR a)]. }
assert (BT : forall b, branch_taken BC_LTU (sv_denot E (SOff 553 0))
   (sv_denot E (SAlu ALU_SRL (SAlu ALU_SLL (SOff 555 0) (SLit 32)) (SLit 32))) = b -> b = (n_cap cx <? r)).
{ intros b Hb. rewrite branch_ltu_U, nxs_U_zext32, E25 in Hb.
  rewrite (U_atom E 553 (n_cap cx) E23) in Hb by (unfold NX_CAP_MAX in Hcap0; lia). symmetry. exact Hb. }
psrr_branch_tok RUN BR HS SHOK NXS_SPAN.
- (* cap < r: the chunk is cap, already in s11 *)
  pose proof (BT true Hc) as Hlt. symmetry in Hlt. apply Z.ltb_lt in Hlt. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK NXS_SPAN NP_skc; [nxs_awr U60 Hsp1 Hsp0|].
  nxs_reg HS (27%bv : bv 5) (SOff 553 0) H27.
  apply (LANDC _ ms _ HS); [vm_compute; reflexivity | vm_compute; reflexivity
    | apply (nx_sr_ok_std B KS cx fp HB _ _ HE); vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | exact HJ | | |].
  + rewrite H27, nx_sv_SOff0, E23, Z.min_l by lia. reflexivity.
  + intros a Ha Hs. rewrite <- (EQ1 a Ha Hs).
    apply (nx_keep_out B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 HFRM E true NSH_ph 0 0 0 []
      [nx_ps_region 0 nxs_pcs] (ms_mem ms1) (ms_mem ms) HE HEI HFr a Ha Hs); [lia | lia | exact (NOWR a)].
  + exact (proj1 (ne_wb_md _ _ _)).
  + exact (proj2 (ne_wb_md _ _ _)).
- (* r <= cap: the chunk is r (mv s11,a0 0x81ad4) *)
  pose proof (BT false Hc) as Hge. symmetry in Hge. apply Z.ltb_ge in Hge. clear Hc.
  paj_run_to_tok RUNTO HS HJ SHOK NXS_SPAN NP_skc; [nxs_awr U60 Hsp1 Hsp0|].
  nxs_reg HS (27%bv : bv 5) (SAlu ALU_ADD (SAlu ALU_SRL (SAlu ALU_SLL (SOff 555 0) (SLit 32)) (SLit 32)) (SLit 0)) H27.
  apply (LANDC _ ms _ HS); [vm_compute; reflexivity | vm_compute; reflexivity
    | apply (nx_sr_ok_std B KS cx fp HB _ _ HE); vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity
    | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | | exact HJ | | |].
  + rewrite H27, denot_lit_U, nxs_U_add0, nxs_U_zext32, E25, Z.min_r by lia. reflexivity.
  + intros a Ha Hs. rewrite <- (EQ1 a Ha Hs).
    apply (nx_keep_out B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 HFRM E true NSH_ph 0 0 0 []
      [nx_ps_region 0 nxs_pcs] (ms_mem ms1) (ms_mem ms) HE HEI HFr a Ha Hs); [lia | lia | exact (NOWR a)].
  + exact (proj1 (ne_wb_md _ _ _)).
  + exact (proj2 (ne_wb_md _ _ _)).
Qed.

Lemma nxs_tail : forall (R : ncx -> Z -> Prop) r,
  FROM (nx_empty_inv B MT KS R) -> FROM (nx_exit_inv B MT KS) ->
  (forall r', 0 < r' < r -> FROM (nx_sk0_inv B MT KS R r')) ->
  FROM (nx_skc_inv R r).
Proof.
intros R r HEMP HEX IH cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HFRM HI.
destruct HI as (Hc0 & (q & lh & Hnext & Hch & Hq16 & Hinz & Hcap & Hr & HM & R20 & R21 & R22 & R23 & R25 & R26) & R27).
pose proof HM as (HBD & H24 & HJB & HK & HEn & Hh & Hps & Hpsra & Hsrc & Hq & Hbuf & Hts).
pose proof HJB as (Hk2 & HJB_ab & Hmo & Hfd3 & Hfs3).
pose proof HBD as (HB0 & Hsl). pose proof HB0 as HB0'. unfold nx_body0 in HB0'.
destruct HB0' as (Hpc & Hresv & Hsvc & Hrom & Hfr & Hfc & Hregs & Hsaved & Hhdr & Hflag & Hsh & Hlen & H18 & H19 & HF0).
destruct (nxs_seat cx fp k2 ly3 S3 W3 ms3 md3 NP_skc _ _ _ _ _ HB HJ HFRM HM R21) as (EPS & EH & HS & SHOK).
destruct (nxs_env cx fp ms3) as (HE & HEI).
destruct (nxs_geo cx HB Hh) as (Hsp1 & Hsp0 & HEb & Hspc & Hsp47).
pose proof (nxs_U60 cx fp _ HB Hh HE) as U60.
pose proof (nxs_SH24 cx fp _ HB HE EPS) as SH24.
assert (Hcap0 : 0 <= n_cap cx <= NX_CAP_MAX).
{ pose proof HB as HB'. unfold nx_base in HB'. decompose [and] HB'.
  match goal with H : n_h cx <> 0 -> In (n_buf cx, _) _ /\ _ |- _ => destruct (H Hh) as (_ & _ & _ & _ & _ & Hc & _) end. exact Hc. }
remember (Z.min (n_cap cx) r) as nk eqn:Hn_def.
assert (Hn1 : 0 < nk) by (subst nk; lia).
assert (Hn2 : nk <= n_cap cx) by (subst nk; lia).
assert (Hn3 : nk <= r) by (subst nk; lia).
assert (Hn4 : nk = n_cap cx \/ nk = r) by (subst nk; lia).
set (E := nxs_E cx fp ms3) in *.
assert (E557 : ew E 557%nat = w64 nk)
  by (change 557%nat with (NA_CUR + 27)%nat; unfold E; rewrite (nxs_E_cur cx fp ms3 27 27%bv ltac:(lia) eq_refl); exact R27).
assert (E25 : bv_unsigned (ew E 555%nat) mod 2 ^ 32 = r)
  by (change 555%nat with (NA_CUR + 25)%nat; unfold E; rewrite (nxs_E_cur cx fp ms3 25 25%bv ltac:(lia) eq_refl); exact R25).
pose proof HJ as HJ3.
assert (NOWR : forall a, ~ in_wrange E [nx_ps_region 0 nxs_pcs] a)
  by (intros a (rr & [<- | []] & Hrr); cbn in Hrr; lia).
(* 0x81ad8 .. 0x81af0: the shadow of ps (the token), a3 := ps->f, the call fread(buf, 1, n, h) *)
paj_run_tok RUN HS HJ SHOK NXS_SPAN; [nxs_awr U60 Hsp1 Hsp0|].
rename ms into ms2, HF into HF2, HFr into HFr2, HG into HG2.
  (* the memory at the call: only the spill slots may have changed since NP_skc *)
  assert (EQ2 : forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx <= a < n_sp1 cx + NX_SPILL) ->
    aview SEGS (w_H W3) (ms_mem ms2) a = aview SEGS (w_H W3) (ms_mem ms3) a).
  { intros a Ha Hs.
    apply (nx_keep_out B KS LAWS cx fp k2 ly3 S3 W3 ms3 md3 HB HJ3 HFRM E true NSH_ph 0 0 0 []
      [nx_ps_region 0 nxs_pcs] (ms_mem ms3) (ms_mem ms2) HE HEI HFr2 a Ha Hs); [lia | lia | exact (NOWR a)]. }
  assert (HPW2 : forall a, spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx) -> apresent (w_H W3) (ms_mem ms2) a).
  { intros a Ha. pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
    apply Hpres. revert Ha Hsp0; clear; intros; lia. }
  destruct (nxs_mid_mem_out cx fp k2 ly3 S3 W3 (ms_mem ms3) md3 (ms_mem ms2) (q + 16 + nx_incl cx q - r)
    (nx_ol cx (Some q)) (n_lvt cx) (n_lvid cx) (n_tsv cx) HB Hh HJ3
    ltac:(intros a Ha Hw; apply EQ2; [exact Ha | revert Hw Hsp1; clear; unfold NX_STK, AFREAD_STK, NX_SPILL; intros; lia])
    HPW2 ASIL HK Hps Hpsra Hsrc Hbuf Hts) as (HK2 & Hps2 & Hpsra2 & Hsrc2 & Hbuf2 & Hts2).
  (* the registers at the call *)
  pmkst HS.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (11%bv : bv 5) Q11.
  prreg HS (12%bv : bv 5) Q12. prreg HS (13%bv : bv 5) Q13.
  assert (SPc : spZ (ms_regs ms2) = n_sp1 cx) by (unfold spZ; rewrite Q2; exact U60).
  assert (EB : forall n (rr : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned rr -> ew E n = getr (n_regs cx) rr).
  { intros n rr Hn Hnr. rewrite (proj1 HE n Hn). pose proof HB as HB'. unfold nx_base in HB'. decompose [and] HB'.
    match goal with HE0 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew (n_E0 cx) n = getr (n_regs cx) r |- _ =>
      exact (HE0 n rr Hnr) end. }
  assert (HBr : getr (n_regs cx) 3 = w64 (as_gp B) /\ getr (n_regs cx) 4 = w64 (as_tp B) /\ 4096 <= raZ (n_regs cx)).
  { pose proof HB as HB'. unfold nx_base in HB'. decompose [and] HB'. repeat split; assumption. }
  assert (E550 : ew E 550%nat = w64 (n_buf cx))
    by (change 550%nat with (NA_CUR + 20)%nat; unfold E; rewrite (nxs_E_cur cx fp ms3 20 20%bv ltac:(lia) eq_refl); exact R20).
  pose proof pa_B_ok as (HBa0 & HBa1 & _). pose proof (pa_base_lo (PL := PL_pcap) (PI := PI)) as HBLO.
  destruct (nx_fread_buf_pre B KS LAWS cx fp k2 ly3 S3 W3 (ms_mem ms2) _ nk HB Hh HJ HJB_ab ltac:(lia))
    as (Pin_h & Pin_b & Pbw & Pwr & Pnm & Pdest).
  assert (Hsp8 : 0 <= spZ (n_regs cx) - 16 /\ spZ (n_regs cx) <= 2 ^ 47).
  { pose proof asan_consts as (C1 & _). revert Hspc Hsp47 C1. clear. unfold NX_STK, AFREAD_STK. intros. lia. }
  assert (RW8 : forall o, 8 <= o <= 16 -> rdword (aview SEGS (w_H W3) (ms_mem ms2)) (spZ (n_regs cx) - o) =
    rdword (aview SEGS (w_H W3) (ms_mem ms3)) (spZ (n_regs cx) - o)).
  { intros o Ho. apply rdword_ext. intros kk Hk. apply EQ2.
    - pose proof asan_consts as (C1 & _). revert Ho Hk Hspc Hsp47 C1. clear. unfold NX_STK, AFREAD_STK. intros. lia.
    - revert Ho Hk Hsp1. clear. unfold NX_SPILL. intros. lia. }
  assert (HACH : achain ly3 (aview SEGS (w_H W3) (ms_mem ms2)) (n_sp1 cx) (spZ (n_regs cx)) (nx_ch cx)).
  { apply (nx_achain_call B KS LAWS cx fp k2 ly3 S3 W3 (ms_mem ms2) _ HB Hh HJ HK2).
    - rewrite (RW8 8 ltac:(lia)). exact (proj1 Hsaved).
    - rewrite (RW8 16 ltac:(lia)). replace (spZ (n_regs cx) - 16) with (spZ (n_regs cx) - 16 - 8 * 0) by lia.
      rewrite (proj2 Hsaved 0 ltac:(lia)). reflexivity. }
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) ?mdq) _ =>
    change (mkCfg (mkst rg (Z_to_bv 64 (pa_sigma PS___interceptor_trampoline_fread)) mm (seg_rom SEGS)) mdq)
      with (cfg_at SEGS (pa_sigma PS___interceptor_trampoline_fread) rg mm mdq);
    eapply SRr_bind;
    [ apply (AFREAD (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
        ((NX_CID, fp) :: n_own cx) ly3 S3 W3 mm mdq k2 rg (nx_ch cx) (n_buf cx) nk (n_h cx) (n_b cx)
        (q + 16 + nx_incl cx q - r) (n_C cx)) | ]
  end.
  { unfold afread_pre, rread_call. rewrite !SPc.
    split.
    { split; [exact HJ|].
      split; [rewrite Q1; apply ret_ok_codeptr_v; [lia | reflexivity]|].
      split; [unfold raZ; rewrite Q1, unsigned_lit_small by (revert HBa0 HBa1; clear; intros; lia); revert HBLO; clear; intros; lia|].
      split; [rewrite Q3, (EB 3%nat (3%bv : bv 5) ltac:(lia) eq_refl); exact (proj1 HBr)|].
      split; [rewrite Q4, (EB 4%nat (4%bv : bv 5) ltac:(lia) eq_refl); exact (proj1 (proj2 HBr))|].
      split; [unfold n_sp1, nx_sp1; rewrite Z.mul_comm; replace (((spZ (n_regs cx) - NX_MFRAME) / 32) * 32) with
               ((((spZ (n_regs cx) - NX_MFRAME) / 32) * 2) * 16) by lia; apply Z.mod_mul; lia|].
      split; [revert Hsp1 Hsp0; clear; unfold NX_STK, AFREAD_STK; intros; lia|].
      split; [revert Hsp1 Hsp0; clear; intros; lia|].
      unfold s0Z. rewrite Q8, (EB 2%nat (2%bv : bv 5) ltac:(lia) eq_refl). fold (spZ (n_regs cx)). exact HACH. }
    split; [rewrite Q10, E550; reflexivity|].
    split; [rewrite Q11; reflexivity|].
    split; [rewrite Q12, E557; reflexivity|].
    split; [rewrite Q13; exact EH|].
    split; [exact Pin_h|]. split; [exact Pin_b|]. split; [exact Pbw|]. split; [exact Hsrc2|].
    split; [exact Pwr|]. split; [exact Pnm | exact Pdest]. }
  intros W4 c4 Hwle (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & HK4 & HQ4).
  destruct HQ4 as (-> & -> & Hx10 & Hgarr & Hsrc4 & _ & _ & Hfd4 & Hfs4 & Hband).
  rewrite SPc in HK4.
  assert (HKO : acall_keptO SEGS B ly3 S3 W3 (ms_mem ms2) W4 mem4 (n_sp1 cx - AFREAD_STK) (n_sp1 cx)
    (rread_wrset (n_h cx) (n_buf cx) nk)).
  { assert (Hbn : nk <= nx_bufn (n_cap cx)) by (unfold nx_bufn; revert Hn2; clear; intros; lia).
    assert (WEb : forall a, rread_wrset (n_h cx) (n_buf cx) nk a -> a < alloc_ceiling).
    { intros a Ha. apply HEb. unfold nx_E, nx_wrset. destruct Ha as [Ha|Ha];
        [right; right; right; split; [exact Hh | exact Ha] | right; left; revert Ha Hbn; clear; intros; lia]. }
    destruct HK4 as (K1 & K2 & K3 & K4 & K5 & K6).
    split; [intros a Ha Hw; apply K1; [exact Ha | exact Hw | intros X; pose proof (WEb a X) as Y; revert Ha Y; clear; intros; lia]|].
    exact (conj K2 (conj K4 (conj K5 K6))). }
  assert (Hbn : nk <= nx_bufn (n_cap cx)) by (unfold nx_bufn; revert Hn2; clear; intros; lia).
  pose proof HJ3 as (HAR3 & Hly3 & _).
  pose proof HB as HBc. unfold nx_base in HBc. destruct HBc as (HJ0 & _).
  pose proof HJ0 as (_ & Hly0 & _).
  assert (EFA : forall c p, frame_addr ly3 c p = frame_addr (n_lyc cx) c p).
  { intros c p. rewrite (frame_addr_layout_le _ _ _ Hly3 c p). symmetry. exact (frame_addr_layout_le _ _ _ Hly0 c p). }
  assert (HinF : In (NX_CID, fp) (frames S3)) by (rewrite HFRM; left; reflexivity).
  assert (FSB : fs_frame_bytes NX_CID = 64) by reflexivity.
  destruct (frames_bounds SEGS B LAWS _ _ _ _ _ NX_CID fp HAR3 HinF) as (HF4 & HFc & HFapp).
  rewrite EFA in HF4, HFc, HFapp. rewrite FSB in HFc, HFapp. fold (nF cx fp) in HF4, HFc, HFapp.
  pose proof (nxb_buf B KS cx HB Hh) as Hbufb.
  assert (HinbS : In (n_buf cx, nx_bufn (n_cap cx)) (ablocks B ly3 S3)) by (rewrite HJB_ab; exact (proj1 Hbufb)).
  assert (HinhS : In (n_h cx, SRC_FILE_BLOCK) (ablocks B ly3 S3)) by exact Pin_h.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ NX_CID fp HAR3 HinbS HinF) as Dbf.
  pose proof (sep_block_frame SEGS B LAWS _ _ _ _ _ _ _ NX_CID fp HAR3 HinhS HinF) as Dhf.
  unfold zdisjoint in Dbf, Dhf. cbn [fst snd] in Dbf, Dhf. rewrite EFA, FSB in Dbf, Dhf. fold (nF cx fp) in Dbf, Dhf.
  change (req_size SRC_FILE_BLOCK) with 1304 in Dhf.
  pose proof (req_size_bounds (nx_bufn (n_cap cx)) ltac:(unfold nx_bufn; lia)) as (_ & _ & Hrb & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HinbS) as (_ & _ & _ & Hbapp & _).
  destruct (al_blocks _ _ LAWS _ _ _ _ _ _ _ HAR3 HinhS) as (_ & _ & _ & Hhapp & _).
  change (req_size SRC_FILE_BLOCK) with 1304 in Hhapp.
  assert (HnSH : nSH cx fp = shadow_addr (nF cx fp)) by reflexivity.
  assert (E2 : bv_unsigned (ew E 2%nat) = spZ (n_regs cx)) by (rewrite (EB 2%nat (2%bv : bv 5) ltac:(lia) eq_refl); reflexivity).
  assert (E516 : bv_unsigned (ew E NA_F) = nF cx fp).
  { rewrite (proj1 (proj2 (proj2 (proj2 HE)))). unfold w64. apply unsigned_lit_small.
    pose proof asan_consts as (C1 & _). revert HF4 HFc C1. clear. intros. lia. }
  assert (E529 : bv_unsigned (ew E NA_FSH) = nSH cx fp).
  { rewrite (proj2 (proj2 (proj2 (proj2 (proj2 HE))))). unfold w64. apply unsigned_lit_small.
    revert HF4 HFc. clear. unfold nSH, nF, shadow_of_addr, SHADOW_OFF. intros. pose proof asan_consts as (C1 & _).
    assert (0 <= frame_addr (n_lyc cx) NX_CID fp / 8 <= 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia). lia. }
  jafter_call_keep_pi HS 64%nat regs4 (mrestrict (w_H W4) mem4) HP4 [0; 1; 2; 3]%nat HS2.
  match type of HS2 with ?tq -> _ => assert (HRK : tq); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; try apply Forall_nil.
    - apply (region_kept_stack_ajO SEGS B E ly3 S3 W3 (ms_mem ms2) W4 mem4 (n_sp1 cx - AFREAD_STK) (n_sp1 cx) _ 2%nat
        (-104) 0 0 0 _ (n_sp0 cx) (spZ (n_regs cx)) (n_STK cx) _ _ _ _ _ _ _ _ _ _ _ HKO HJ4 E2);
        revert Hsp1 Hsp0; clear; unfold NX_STK, AFREAD_STK; intros; lia.
    - apply (region_kept_stack_ajO SEGS B E ly3 S3 W3 (ms_mem ms2) W4 mem4 (n_sp1 cx - AFREAD_STK) (n_sp1 cx) _ 60%nat
        0 120 0 120 _ (n_sp0 cx) (n_sp1 cx) (n_STK cx) _ _ _ _ _ _ _ _ _ _ _ HKO HJ4 U60);
        revert Hsp1 Hsp0; clear; unfold NX_STK, AFREAD_STK; intros; lia.
    - apply (region_kept_frame_ajO SEGS B E ly3 S3 W3 (ms_mem ms2) W4 mem4 (n_sp1 cx - AFREAD_STK) (n_sp1 cx) _ 516%nat
        0 64 0 0 _ (nF cx fp) NX_CID fp HKO E516 HinF); [rewrite EFA; fold (nF cx fp); lia | rewrite EFA, FSB; fold (nF cx fp); lia | lia |].
      intros a Ha [X|X]; [revert Ha X Dhf; unfold SRC_FILE_BLOCK; clear; intros; lia | revert Ha X Dbf Hbn Hrb; clear; intros; lia].
    - apply (region_kept_ownframe_ajO SEGS B E ly3 S3 W3 (ms_mem ms2) W4 mem4 (n_sp1 cx - AFREAD_STK) (n_sp1 cx) _ 529%nat
        0 8 0 0 _ (nSH cx fp) NX_CID fp HKO E529 HinF).
      + right. rewrite EFA, FSB. fold (nF cx fp). rewrite HnSH. change (64 / 8) with 8. lia.
      + intros a Ha [X|X].
        * revert Ha X Hhapp HF4 HFc HnSH. unfold SRC_FILE_BLOCK, in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL.
          clear. intros. pose proof asan_consts as (C1 & _).
          pose proof (Z.mul_div_le (nF cx fp) 8 ltac:(lia)) as Hd8. pose proof (Z.div_pos (nF cx fp) 8 ltac:(lia) ltac:(lia)) as Hd0. lia.
        * revert Ha X Hbapp Hbn Hrb HF4 HFc HnSH. unfold in_app, shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL.
          clear. intros. pose proof asan_consts as (C1 & _).
          pose proof (Z.mul_div_le (nF cx fp) 8 ltac:(lia)) as Hd8. pose proof (Z.div_pos (nF cx fp) 8 ltac:(lia) ltac:(lia)) as Hd0. lia.
      + intros a Ha. lia. }
  rewrite <- restrict_mkst_fx in HS2. rewrite Q1.
  (* ---- after the call: 0x81af4 `bne a0,s11`, 0x81af8 `subw s9,s9,s11`, 0x81afc `bnez s9` ---- *)
  pose (p := q + 16 + nx_incl cx q - r).
  pose (j := rread_k nk (Z.of_nat (length (n_C cx))) p).
  assert (Hjdef : j = Z.min nk (Z.of_nat (length (n_C cx)) - p)) by reflexivity.
  change (rread_k nk (Z.of_nat (length (n_C cx))) (q + 16 + nx_incl cx q - r)) with j in Hx10, Hgarr, Hsrc4.
  change (q + 16 + nx_incl cx q - r) with p in Hgarr, Hsrc4, Hsrc2, Hps2.
  assert (Lws : length (map (getr regs4) CLOB) = 16%nat) by (rewrite length_map; reflexivity).
  pose (Ec := havoc E 64 (map (getr regs4) CLOB)).
  change (havoc E 64 (map (getr regs4) CLOB)) with Ec in HS2.
  assert (HE2 : nx_env cx fp Ec) by (apply nx_env_havoc; [exact HE | lia | rewrite Lws; right; lia | rewrite Lws; unfold A_TEXT; lia]).
  assert (HEI2 : img_env VAL A_LIM Ec) by (apply img_env_havoc; [exact HEI | rewrite Lws; unfold A_TEXT; lia]).
  assert (AG2 : forall i, (80 <= i)%nat -> ew Ec i = ew E i) by (intros i Hi; apply ew_havoc_above; rewrite Lws; lia).
  assert (EPS2 : ew Ec NA_PS = w64 (n_ps cx)) by (unfold Ec; rewrite ew_havoc_old by (unfold NA_PS; lia); exact EPS).
  assert (Ec68 : ew Ec 68%nat = w64 j).
  { unfold Ec. change 68%nat with (64 + 4)%nat. rewrite (ew_havoc_new E 64 _ 4 (w64 0)) by (rewrite Lws; lia).
    cbn [CLOB map nth]. exact Hx10. }
  assert (Ec557 : ew Ec 557%nat = w64 nk) by (rewrite AG2 by lia; exact E557).
  pose proof (nxs_U60 cx fp Ec HB Hh HE2) as U60b.
  assert (U60c : bv_unsigned (ew Ec 60%nat) = n_sp1 cx) by exact U60b.
  pose proof (nxs_SH24 cx fp Ec HB HE2 EPS2) as SH24b.
  (* the model: the count, and the stream after the call *)
  assert (HpC : n_p cx <= p <= Z.of_nat (length (n_C cx))) by exact Hq.
  assert (Hp0 : 0 <= n_p cx).
  { pose proof HB as HB'. unfold nx_base in HB'. decompose [and] HB'.
    match goal with H : n_h cx <> 0 -> In (n_h cx, SRC_FILE_BLOCK) _ /\ _ |- _ => destruct (H Hh) as (_ & _ & _ & _ & Hpp & _) end. exact (proj1 Hpp). }
  destruct (nxs_turn_model (n_sw cx =? 1) (n_C cx) (n_cap cx) q r nk p Hq16 Hinz Hcap Hr Hc0 (proj1 Hcap0) Hn_def eq_refl
    ltac:(lia)) as (MCUT & MBIG & Mj).
  fold (nx_incl cx q) in MCUT, MBIG.
  assert (Hj : 0 <= j <= nk) by (rewrite Hjdef; exact Mj).
  (* the memory after the call *)
  assert (HlR : Z.of_nat (length (firstn (Z.to_nat j) (skipn (Z.to_nat p) (n_C cx)))) = j).
  { rewrite length_firstn, length_skipn. rewrite Hjdef. revert HpC Hp0 Mj. clear. intros. lia. }
  destruct (nx_fread_buf_post B KS LAWS cx fp k2 ly3 S3 W3 (ms_mem ms2) _ W4 mem4 md4 nk j _ _ _ _ _
    HB Hh HJ HFRM HJB_ab ltac:(lia) HK4 Hband (proj1 HJ4) Hgarr HlR Hj HK2 Hps2 Hpsra2 Hts2)
    as (HK5 & Hps5 & Hpsra5 & Hbuf5 & Hts5).
  assert (Hbuf5' : exists bj', garr8 SEGS (rdW W4 mem4) (n_buf cx) bj' /\ length bj' = length (n_bj cx)).
  { destruct Hbuf2 as (bj0 & Hg0 & Hl0). destruct (Hbuf5 bj0 Hg0 Hl0) as (bj' & Hg' & Hl' & _). exists bj'. split; assumption. }
  assert (SHOK2 : sh_ok SEGS nx_Bx (nx_SH ++ []) Ec (rdW W4 mem4))
    by (apply (nx_shok B KS cx fp W4 (mkst regs4 (Z_to_bv 64 (VAL A_TEXT + (symaddr ((Symbols.Asan.s_pcap_source_next + 0x2d8) - Symbols.Asan.s_libreac_fuzz_fopen)%Z))) mem4 (seg_rom SEGS)) HB Ec [] HE2 Hpsra5);
        constructor).
  clear HS. rename HS2 into HS.
  (* the landing after the call: the middle state at the target pc, the stream at p + j *)
  assert (HQpj : n_p cx <= p + j <= Z.of_nat (length (n_C cx))).
  { pose proof (Z.min_spec nk (Z.of_nat (length (n_C cx)) - p)) as M2. rewrite Hjdef. revert HpC Hj M2 Hjdef. clear. intros. lia. }
  assert (LANDP : forall ss (m : machine_state) md',
    st_ok_pi SEGS VAL Ec ss (restrict (w_H W4) m) -> ss_resv ss = None ->
    nx_sr_ok cx fp Ec (ss_regs ss) -> nx_land_chk true NSH_ph (ss_mem ss) = true ->
    sr_get (ss_regs ss) 24 = nx_shx (SOff NA_PS 0) ->
    ajournal SEGS B (n_STK cx) (n_sp0 cx) (n_FP cx) (n_ly cx) (n_S cx) (n_W0 cx) (n_mem0 cx) (n_md0 cx)
      ((NX_CID, fp) :: n_own cx) ly3 S3 W4 (ms_mem m) md' k2 ->
    (forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx <= a < n_sp1 cx + NX_SPILL) ->
       aview SEGS (w_H W4) (ms_mem m) a = aview SEGS (w_H W4) mem4 a) ->
    m_fds md' = m_fds md4 -> m_fs md' = m_fs md4 ->
    nx_mid B MT KS cx fp (ss_pc ss) NSH_ph (nx_E cx) (p + j) (nx_ol cx (Some q)) (n_lvt cx) (n_lvid cx) (n_tsv cx)
      k2 ly3 S3 W4 m md').
  { intros ss m md' HSm Hrv Hsr Hchk G24 HJm HEQ Hfd Hfs.
    assert (HPW : forall a, spZ (n_regs cx) - NX_STK <= a < spZ (n_regs cx) -> apresent (w_H W4) (ms_mem m) a).
    { intros a Ha. pose proof HJm as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
      apply Hpres. revert Ha Hsp0; clear; intros; lia. }
    destruct (nxs_mid_mem_out cx fp k2 ly3 S3 W4 mem4 md4 (ms_mem m) (p + j) (nx_ol cx (Some q)) (n_lvt cx) (n_lvid cx)
      (n_tsv cx) HB Hh HJ4
      ltac:(intros a Ha Hw; apply HEQ; [exact Ha | revert Hw Hsp1; clear; unfold NX_STK, AFREAD_STK, NX_SPILL; intros; lia])
      HPW ASIL HK5 Hps5 Hpsra5 Hsrc4 Hbuf5' Hts5) as (HKm & Hpsm & Hpsram & Hsrcm & Hbufm & Htsm).
    assert (H24m : sv_denot Ec (sr_get (ss_regs ss) 24) = w64 (shadow_of_addr SHADOW_OFF (n_ps cx))) by (rewrite G24; exact SH24b).
    assert (Hfdm : m_fds md' = m_fds (n_mdc cx)).
    { rewrite Hfd, Hfd4. first [exact Hfd3 | rewrite (proj1 (ne_wb_md _ _ _)); exact Hfd3]. }
    assert (Hfsm : m_fs md' = m_fs (n_mdc cx)).
    { rewrite Hfs, Hfs4. first [exact Hfs3 | rewrite (proj2 (ne_wb_md _ _ _)); exact Hfs3]. }
    exact (nxs_land cx fp k2 ly3 S3 W4 m md' Ec ss (p + j) (nx_ol cx (Some q)) (n_lvt cx) (n_lvid cx) (n_tsv cx)
      HB HJm HFRM HE2 HEI2 HSm Hrv Hsr Hchk H24m Hk2 HJB_ab Hmo Hfdm Hfsm HKm Hh Hpsm Hpsram Hsrcm HQpj Hbufm Htsm). }
  (* a run after the call writes no byte outside the spill slots *)
  assert (KEEP2 : forall rs (m m' : word -> option byte),
    frame_of Ec rs (rdW W4 m) (rdW W4 m') ->
    (forall b wlo whi x, In (b, wlo, whi) (windows rs) -> base_val Ec b + wlo <= x < base_val Ec b + whi ->
       n_sp1 cx <= x < n_sp1 cx + NX_SPILL) ->
    forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx <= a < n_sp1 cx + NX_SPILL) ->
      aview SEGS (w_H W4) m' a = aview SEGS (w_H W4) m a).
  { intros rs m0 m1 HFm Hw a Ha Hs. exact (YC4b.kept_of_frame (segs := SEGS) Ec rs (w_H W4) m0 m1 _ HFm Hw a Ha Hs). }
  Local Ltac nxs_win U60c :=
    let b := fresh "bw" in let wlo := fresh "wlo" in let whi := fresh "whi" in let x := fresh "xw" in
    let Hin := fresh "Hinw" in let Hrg := fresh "Hrgw" in
    intros b wlo whi x Hin Hrg;
    lazymatch type of Hin with In _ (windows ?rs) =>
      let rs' := eval vm_compute in (windows rs) in change (In (b, wlo, whi) rs') in Hin end;
    repeat (let Hq := fresh "Hqw" in destruct Hin as [Hq|Hin];
      [injection Hq as <- <- <-; cbn [base_val] in Hrg;
       first [revert Hrg; clear; intros; lia
             | rewrite U60c in Hrg; unfold NX_SPILL; revert Hrg; clear; intros; lia] |]);
    destruct Hin.
  (* the registers the turn keeps *)
  assert (AGc : forall i, (20 <= i < 32)%nat -> ew Ec (NA_CUR + i) = ew (nxs_E cx fp ms3) (NA_CUR + i))
    by (intros i Hi; apply AG2; unfold NA_CUR; lia).
  assert (BT2 : forall b, branch_taken BC_NE (sv_denot Ec (SOff 68 0)) (sv_denot Ec (SOff 557 0)) = b -> b = negb (j =? nk)).
  { intros b Hb. rewrite branch_ne_U in Hb.
    rewrite (U_atom Ec 68 j Ec68), (U_atom Ec 557 nk Ec557) in Hb by (unfold NX_CAP_MAX in *; lia). symmetry. exact Hb. }
  psrr_branch_tok RUN BR HS SHOK2 NXS_SPAN.
  - (* j <> nk: a short read (KCutBig), to the exit join 0x81d24 *)
    pose proof (BT2 true Hc) as Hjn. symmetry in Hjn. apply negb_true_iff, Z.eqb_neq in Hjn. clear Hc.
    destruct (MCUT ltac:(rewrite <- Hjdef; exact Hjn)) as (HKc & Hpj). rewrite <- Hjdef in Hpj.
    paj_run_to_tok RUNTO HS HJ4 SHOK2 NXS_SPAN NP_exit; [nxs_awr U60b Hsp1 Hsp0|].
    apply (HEX cx fp k2 ly3 S3 W4 ms _ HB HJ4 HFRM).
    assert (HKB : PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KBig0 \/
                  PSN.kind (n_sw cx =? 1) (nxF (n_C cx)) (n_cap cx) q = PSN.KCutBig) by (right; exact HKc).
    destruct (nxs_exit_model (n_sw cx =? 1) (n_C cx) (n_cap cx) (n_p cx) q lh (n_lol cx) (n_lvt cx) (n_lvid cx) (n_tsv cx)
      Hch ltac:(lia) HKB) as (Eres & Epos & Eorig & Efit & Evt & Evid & Ets).
    apply (nxs_exit_of_mid cx fp q (p + j)).
    + lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
        assert (Hpc' : ss_pc ss = NP_exit) by (vm_compute; reflexivity); rewrite <- Hpc' end.
      apply (LANDP _ ms _ HS); [vm_compute; reflexivity | apply (nx_sr_ok_std B KS cx fp HB _ _ HE2); vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | exact HJ4 | | |].
      * apply (KEEP2 _ _ _ HFr). nxs_win U60c.
      * rewrite (proj1 (ne_wb_md _ _ _)). reflexivity.
      * rewrite (proj2 (ne_wb_md _ _ _)). reflexivity.
    + rewrite <- R22. apply (nxs_reg_land cx fp ms3 W4 ms _ Ec 22 22%bv ltac:(lia) eq_refl HS); [vm_compute; reflexivity | apply AGc; lia].
    + exact Eres.
    + rewrite Epos. unfold PSN.pos_of. rewrite HKc. unfold PSN.flen. rewrite nxF_length. lia.
    + exact Eorig.
    + exact Efit.
    + exact Evt.
    + exact Evid.
    + exact Ets.
  - (* j = nk: s9 -= nk, then `bnez s9` *)
    pose proof (BT2 false Hc) as Hjn. symmetry in Hjn. apply negb_false_iff, Z.eqb_eq in Hjn. clear Hc.
    paj_run_tok RUN HS HJ4 SHOK2 NXS_SPAN; [nxs_awr U60b Hsp1 Hsp0|].
    rename ms into ms5, HFr into HFr5.
    assert (EQ5 : forall a, 0 <= a < 2 ^ 64 -> ~ (n_sp1 cx <= a < n_sp1 cx + NX_SPILL) ->
      aview SEGS (w_H W4) (ms_mem ms5) a = aview SEGS (w_H W4) mem4 a) by (apply (KEEP2 _ _ _ HFr5); nxs_win U60c).
    pose proof (nxs_incl_range (n_sw cx =? 1) (nxF (n_C cx)) q) as Hinr. fold (nx_incl cx q) in Hinr.
    assert (U555 : U Ec (SOff 555 0) = bv_unsigned (ew E 555%nat)) by (unfold U; rewrite nx_sv_SOff0, AG2 by lia; reflexivity).
    assert (U557 : U Ec (SOff 557 0) = nk) by (apply (U_atom Ec 557 nk Ec557); unfold NX_CAP_MAX in *; lia).
    assert (HLOW : (U Ec (SOff 555 0) - U Ec (SOff 557 0)) mod 2 ^ 32 = r - nk).
    { rewrite U555, U557, <- Zminus_mod_idemp_l, E25. apply Z.mod_small. lia. }
    assert (BT3 : forall b, branch_taken BC_NE (sv_denot Ec (SAluw ALU_SUB (SOff 555 0) (SOff 557 0))) (sv_denot Ec (SLit 0)) = b ->
      (b = true -> r <> nk) /\ (b = false -> r = nk)).
    { intros b Hb. rewrite branch_ne_U, U_SLit in Hb. change (zcanon 0) with 0 in Hb.
      pose proof (nxs_U_subw_lo Ec (SOff 555 0) (SOff 557 0)) as Hlo. rewrite HLOW in Hlo.
      split; intros ->.
      - intros Hrn. assert (Hz : U Ec (SAluw ALU_SUB (SOff 555 0) (SOff 557 0)) = 0)
          by (apply nxs_U_subw_zero; rewrite HLOW; lia).
        rewrite Hz in Hb. cbn in Hb. discriminate Hb.
      - apply negb_false_iff, Z.eqb_eq in Hb. rewrite Hb in Hlo. rewrite Zmod_0_l in Hlo. lia. }
    psrr_branch_tok RUN BR HS SHOK2 NXS_SPAN.
    + (* r <> nk: back to the skip loop's head with r - nk *)
      pose proof (proj1 (BT3 true Hc) eq_refl) as Hrn. clear Hc.
      paj_run_to_tok RUNTO HS HJ4 SHOK2 NXS_SPAN NP_sk0; [nxs_awr U60b Hsp1 Hsp0|].
      apply (IH (r - nk) ltac:(lia) cx fp k2 ly3 S3 W4 ms _ HB HJ4 HFRM).
      split; [exact Hc0|].
      exists q, lh. split; [exact Hnext|]. split; [exact Hch|]. split; [exact Hq16|].
      split; [exact Hinz|]. split; [exact Hcap|]. split; [lia|].
      split.
      { replace (q + 16 + nx_incl cx q - (r - nk)) with (p + j) by (unfold p; lia).
        lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
          assert (Hpc' : ss_pc ss = NP_sk0) by (vm_compute; reflexivity); rewrite <- Hpc' end.
        apply (LANDP _ ms _ HS); [vm_compute; reflexivity | apply (nx_sr_ok_std B KS cx fp HB _ _ HE2); vm_compute; reflexivity
          | vm_compute; reflexivity | vm_compute; reflexivity | exact HJ4 | | |].
        - intros a Ha Hs. rewrite <- (EQ5 a Ha Hs). apply (KEEP2 _ _ _ HFr); [nxs_win U60c | exact Ha | exact Hs].
        - rewrite (proj1 (ne_wb_md _ _ _)), (proj1 (ne_wb_md _ _ _)). reflexivity.
        - rewrite (proj2 (ne_wb_md _ _ _)), (proj2 (ne_wb_md _ _ _)). reflexivity. }
      split; [rewrite <- R20; apply (nxs_reg_land cx fp ms3 W4 ms _ Ec 20 20%bv ltac:(lia) eq_refl HS); [vm_compute; reflexivity | apply AGc; lia]|].
      split; [rewrite (st_ok_pi_restrict_reg _ Ec _ ms 21%bv HS);
              replace (sr_get _ 21) with (SOff NA_PS 0) by (vm_compute; reflexivity); rewrite nx_sv_SOff0; exact EPS2|].
      split; [rewrite <- R22; apply (nxs_reg_land cx fp ms3 W4 ms _ Ec 22 22%bv ltac:(lia) eq_refl HS); [vm_compute; reflexivity | apply AGc; lia]|].
      split; [rewrite <- R23; apply (nxs_reg_land cx fp ms3 W4 ms _ Ec 23 23%bv ltac:(lia) eq_refl HS); [vm_compute; reflexivity | apply AGc; lia]|].
      split.
      { rewrite (st_ok_pi_restrict_reg _ Ec _ ms 25%bv HS).
        replace (sr_get _ 25) with (SAluw ALU_SUB (SOff 555 0) (SOff 557 0)) by (vm_compute; reflexivity).
        fold (U Ec (SAluw ALU_SUB (SOff 555 0) (SOff 557 0))). rewrite nxs_U_subw_lo. exact HLOW. }
      rewrite <- R26; apply (nxs_reg_land cx fp ms3 W4 ms _ Ec 26 26%bv ltac:(lia) eq_refl HS); [vm_compute; reflexivity | apply AGc; lia].
    + (* r = nk: the whole record is read (KBig): `ph` goes out of scope at NP_empty *)
      pose proof (proj2 (BT3 false Hc) eq_refl) as Hrn. clear Hc.
      pose proof (MBIG ltac:(rewrite <- Hjdef; exact Hjn) (eq_sym Hrn)) as HKb.
      assert (HqB : q + 16 + nx_incl cx q <= Z.of_nat (length (n_C cx))).
      { destruct (nx_kind_big _ _ _ _ HKb) as (_ & _ & Hle & _). unfold PSN.flen in Hle. rewrite nxF_length in Hle.
        exact Hle. }
      paj_run_to_tok RUNTO HS HJ4 SHOK2 NXS_SPAN NP_empty; [nxs_awr U60b Hsp1 Hsp0|].
      apply (HEMP cx fp k2 ly3 S3 W4 ms _ HB HJ4 HFRM).
      exists (q + 16 + nx_incl cx q), (Some q).
      split; [apply Hnext; lia|].
      split.
      { replace (q + 16 + nx_incl cx q) with (p + j) by (unfold p; lia).
        lazymatch type of HS with st_ok_pi _ _ _ ?ss _ =>
          assert (Hpc' : ss_pc ss = NP_empty) by (vm_compute; reflexivity); rewrite <- Hpc' end.
        apply (LANDP _ ms _ HS); [vm_compute; reflexivity | apply (nx_sr_ok_std B KS cx fp HB _ _ HE2); vm_compute; reflexivity
          | vm_compute; reflexivity | vm_compute; reflexivity | exact HJ4 | | |].
        - intros a Ha Hs. rewrite <- (EQ5 a Ha Hs). apply (KEEP2 _ _ _ HFr); [nxs_win U60c | exact Ha | exact Hs].
        - rewrite (proj1 (ne_wb_md _ _ _)), (proj1 (ne_wb_md _ _ _)). reflexivity.
        - rewrite (proj2 (ne_wb_md _ _ _)), (proj2 (ne_wb_md _ _ _)). reflexivity. }
      split; [rewrite <- R20; apply (nxs_reg_land cx fp ms3 W4 ms _ Ec 20 20%bv ltac:(lia) eq_refl HS); [vm_compute; reflexivity | apply AGc; lia]|].
      split; [rewrite (st_ok_pi_restrict_reg _ Ec _ ms 21%bv HS);
              replace (sr_get _ 21) with (SOff NA_PS 0) by (vm_compute; reflexivity); rewrite nx_sv_SOff0; exact EPS2|].
      split; [rewrite <- R23; apply (nxs_reg_land cx fp ms3 W4 ms _ Ec 23 23%bv ltac:(lia) eq_refl HS); [vm_compute; reflexivity | apply AGc; lia]|].
      split; [rewrite <- R26; apply (nxs_reg_land cx fp ms3 W4 ms _ Ec 26 26%bv ltac:(lia) eq_refl HS); [vm_compute; reflexivity | apply AGc; lia]|].
      apply (nx_chain_big _ _ _ _ _ _ Hch); [rewrite nxF_length; lia | lia | exact HKb].
Qed.

(* ---- the phase lemma ---- *)

Theorem pb_skip : forall R : ncx -> Z -> Prop,
  FROM (nx_loop_at B MT KS R) -> FROM (nx_exit_inv B MT KS) -> FROM (nx_sk1_inv B MT KS R).
Proof.
intros R HLOOP HEX.
pose proof (nx_empty_step (SK:=SK) B MT KS LAWS TL ASIL (nx_post SK B MT KS) R HLOOP) as HEMP.
assert (HALL : forall (nr : nat) r, (Z.to_nat r < nr)%nat -> FROM (nx_sk0_inv B MT KS R r)).
{ induction nr as [|nr IHn]; intros r0 Hlt; [lia|].
  apply nxs_head. apply nxs_tail; [exact HEMP | exact HEX |].
  intros r' Hr'. apply IHn. lia. }
apply nx_sk1_step; [|exact HEX].
intros cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF (r & HI).
exact (HALL (S (Z.to_nat r)) r ltac:(lia) cx fp k2 ly3 S3 W3 ms3 md3 HB HJ HF HI).
Qed.

End c.
End b.
End a.
