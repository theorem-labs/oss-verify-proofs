From OSSVerify.Proofs.libreac.fuzz_pcap.lib Require Import SymAddr.
From Stdlib Require Import ZArith List Bool Lia Permutation String.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Cells
  Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.Lib Require Arr.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YL01 YL00 YL0g YI06 YI16 YI14 YI04.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM05 YL0i.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm MemNorm SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel libreac_fuzz_fopen_c
  pcap_source_next_lib pcap_source_next_c pcap_source_close_c rd32f bcmp_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require memmove.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv PTac PGlue PSteps UCut URec USegL
  USegW UGlueT UBridge PInvCF USROcf UContractCF.
Import ListNotations.
Open Scope Z_scope.

(* Glue of the walk: D (0x12e04 -> K4 / K5), L (K4 -> pcap_source_next -> 0x13034), L2 (0x13034 -> K4 / K5),
   W (K5 -> pcap_source_close -> 0x1306c), the walk's loop (ug_walk) and the cut 0x12e04 (ug_K12e3c). *)

Section W.
Context {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

Lemma ud_range : forall g, 0 <= ud g < 256.
Proof. intros g. unfold ud. destruct (g_in g) as [|d l]; [lia|]. apply ss_bz_range. Qed.

Lemma ucap_range : forall g, 0 <= ucap g <= 2040.
Proof. intros g. unfold ucap. pose proof (ud_range g). lia. Qed.

Lemma ures_cases : forall g q,
  (ukind g q = PN.KFit /\ ures g q = PN.rec_len (usw g) (uF g) q /\ 0 < PN.rec_len (usw g) (uF g) q <= ucap g) \/
  (ukind g q <> PN.KFit /\ (ures g q = 0 \/ ures g q = -1)).
Proof.
  intros g q. unfold ures, ukind.
  destruct (PN.kind (usw g) (uF g) (ucap g) q) eqn:K.
  4: left; destruct (PW.kind_fit (usw g) (uF g) (ucap g) q K) as (E & H1 & _); auto.
  all: right; assert (K' : PN.kind (usw g) (uF g) (ucap g) q <> PN.KFit) by (rewrite K; discriminate);
       split; [discriminate | exact (proj2 (PW.kind_nfit (usw g) (uF g) (ucap g) q K'))].
Qed.

Lemma ures_range : forall g q, -1 <= ures g q < 2 ^ 26.
Proof.
  intros g q. pose proof (ucap_range g).
  destruct (ures_cases g q) as [(_ & E & H1)|(_ & [E|E])]; rewrite E; lia.
Qed.

Lemma ures_pos : forall g q, 0 < ures g q <-> ukind g q = PN.KFit.
Proof.
  intros g q.
  destruct (ures_cases g q) as [(K & E & H1)|(K & [E|E])]; rewrite E; split; intros H; try lia; try exact K;
    exfalso; exact (K H).
Qed.

Lemma uafter_fit : forall g p, ukind g (uQ g p) = PN.KFit -> uafter g p = uwalk g (upos g (uQ g p)) ++ uC0 g.
Proof. intros g p K. unfold uafter. rewrite K. reflexivity. Qed.

Lemma uafter_nfit : forall g p, ukind g (uQ g p) <> PN.KFit -> uafter g p = uC0 g.
Proof.
  intros g p K. unfold uafter. destruct (ukind g (uQ g p)) eqn:E; try reflexivity. exfalso. exact (K eq_refl).
Qed.

(* A segment that writes no memory: the actual memory after it equals the one before at every address. *)
Lemma ug_same : forall mem mem', ro_agree rsegs mem -> mem_rel rsegs mem' (normalize rsegs mem) ->
  ro_same rsegs mem mem' -> munch [] mem mem' /\ wmono rsegs mem mem'.
Proof.
  intros mem mem' HRO HR HS.
  assert (E : forall x, mem' x = mem x).
  { apply (mem_unchanged_rel rsegs mem (normalize rsegs mem) mem' (normalize rsegs mem));
      [exact (mem_rel_normalize rsegs mem HRO) | exact HR | exact HS | reflexivity]. }
  split; [intros x _; apply E | apply ss_wmono_eq; exact E].
Qed.

Lemma tr0_bytes : forall m m' a bs, munch [] m m' -> bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof. intros m m' a bs MU H. exact (bytes_at_transport rsegs [] m m' a bs H MU I). Qed.

Lemma tr0_rw : forall m m' a cs, munch [] m m' -> wmono rsegs m m' -> rw_cells rsegs m a cs -> rw_cells rsegs m' a cs.
Proof. intros m m' a cs MU WM H. exact (rw_cells_transport rsegs [] m m' a cs H MU WM I). Qed.

Lemma tr0_ENV : forall g m m', munch [] m m' -> wmono rsegs m m' -> ENV g m -> ENV g m'.
Proof.
  intros g m m' MU WM ((S1 & S2 & S3) & (G1 & gv & G2) & (fl & md & (E1 & E2)) & Q0 & QL).
  split; [split; [exact (tr0_bytes _ _ _ _ MU S1)|]; split; [exact (tr0_bytes _ _ _ _ MU S2) | exact (tr0_bytes _ _ _ _ MU S3)]|].
  split; [split; [exact (tr0_bytes _ _ _ _ MU G1) | exists gv; exact (tr0_bytes _ _ _ _ MU G2)]|].
  split; [exists fl, md; split; [exact (tr0_rw _ _ _ _ MU WM E1) | exact E2]|].
  split; [exact (tr0_bytes _ _ _ _ MU Q0) | exact (tr0_bytes _ _ _ _ MU QL)].
Qed.

Lemma tr0_WKEEP : forall g b buf regs regs' m m', munch [] m m' -> wmono rsegs m m' ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 26 = getr regs 26 ->
  WKEEP g b buf regs m -> WKEEP g b buf regs' m'.
Proof.
  intros g b buf regs regs' m m' MU WM E8 E9 E26 (H8 & H9 & H26 & HE & Q8 & HB & Q24).
  split; [rewrite E8; exact H8|]. split; [rewrite E9; exact H9|]. split; [rewrite E26; exact H26|].
  split; [exact (tr0_ENV _ _ _ MU WM HE)|]. split; [exact (tr0_bytes _ _ _ _ MU Q8)|].
  split; [exact (tr0_bytes _ _ _ _ MU HB) | exact (tr0_bytes _ _ _ _ MU Q24)].
Qed.

Lemma tr0_RECST : forall g b h buf p m m', munch [] m m' -> wmono rsegs m m' ->
  RECST g b h buf p m -> RECST g b h buf p m'.
Proof.
  intros g b h buf p m m' MU WM (HS & HO & (lol & lvt & lvid & pad & HP) & HT & (bj & HU & HL & HF)).
  split; [exact (mstl_transport [] m m' h b (uF g) _ _ _ HS MU WM I I)|].
  split; [exact (tr0_rw _ _ _ _ MU WM HO)|].
  split; [exists lol, lvt, lvid, pad; exact (tr0_rw _ _ _ _ MU WM HP)|].
  split; [exact (tr0_rw _ _ _ _ MU WM HT)|].
  exists bj. split; [exact (Arr.u8arr_transport rsegs [] m m' buf bj HU MU WM I)|]. split; [exact HL | exact HF].
Qed.

(* L2: the walk's call from p answered; on to K4 (a fit record) or K5. *)
Lemma ug_L2 : forall g i p, HC4 B APIf ra empty g i p -> HC5 B APIf ra empty g p -> HC6 B APIf ra empty g i p.
Proof.
  intros g i p H4 H5 c (b & h & buf & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPr).
  destruct HPr as (HWK & HREC & Hi & Hp & Hpn & E10 & E18 & E20 & E25 & E27 & Q8 & Q16 & C32).
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (ss_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof (ures_range g (uQ g p)) as Hn.
  set (n' := ures g (uQ g p)) in *.
  set (Q := fun (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) =>
    m' = normalize rsegs mem /\
    ((0 < n' /\ pc' = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1ec)%Z)) \/ (n' <= 0 /\ pc' = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x400)%Z))) /\
    getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
    getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 13 = wz (ufirst g) /\
    getr R 18 = getr regs 18 /\ getr R 20 = getr regs 20 /\ getr R 21 = wz n' /\
    getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\ getr R 27 = wz (ufirst g)).
  apply (ss_kA_run_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z)) mem md Q (uafter g p) (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (ss_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of.
    eapply evt_mono; [exact (ubs_L2_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) n' (ufirst g) E10 Hn E27)|].
    intros ms [(P & ->) | (P & ->)]; (do 3 eexists; split; [reflexivity|]);
      (split; [reflexivity|]); (split; [first [left; split; [exact P | reflexivity] | right; split; [exact P | reflexivity]]|]);
      repeat split; reflexivity.
  - intros R pc' m' regs' mem' (-> & HB & G2 & G3 & G4 & G8 & G9 & G13 & G18 & G20 & G21 & G25 & G26 & G27)
      XR HR HS.
    destruct (ug_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 3 (HB3 g b h buf) L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
        | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM | intros lo hi y [] ]. }
    assert (K8 : getr regs' 8 = getr regs 8) by (rewrite (ss_getr_eqv _ _ 8 XR); exact G8).
    assert (K9 : getr regs' 9 = getr regs 9) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
    assert (K26 : getr regs' 26 = getr regs 26) by (rewrite (ss_getr_eqv _ _ 26 XR); exact G26).
    pose proof (tr0_WKEEP g b buf regs regs' mem mem' MU WM K8 K9 K26 HWK) as WK'.
    pose proof (tr0_RECST g b h buf p mem mem' MU WM HREC) as RC'.
    destruct HB as [(P & ->) | (P & ->)].
    + assert (K : ukind g (uQ g p) = PN.KFit) by (apply ures_pos; exact P).
      rewrite (uafter_fit g p K). apply H4.
      exists b, h, buf, (wz (ufirst g)). split; [exact Hgood|].
      exists fx', L, A, regs', mem', md. split; [reflexivity|]. split; [exact Hfrm|]. split; [exact FR'|].
      split; [exact HP|].
      split; [exact WK'|]. split; [exact RC'|].
      split; [lia|]. split; [lia|]. split; [exact K|].
      split; [rewrite (ss_getr_eqv _ _ 18 XR); rewrite G18; exact E18|].
      split; [rewrite (ss_getr_eqv _ _ 20 XR); rewrite G20; exact E20|].
      split; [rewrite (ss_getr_eqv _ _ 21 XR); exact G21|].
      split; [rewrite (ss_getr_eqv _ _ 25 XR); rewrite G25; exact E25|].
      split; [rewrite (ss_getr_eqv _ _ 27 XR); exact G27|].
      split; [rewrite (ss_getr_eqv _ _ 13 XR); exact G13|].
      split; [right; split; [lia | reflexivity]|].
      split; [exact (tr0_bytes _ _ _ _ MU Q8)|]. split; [exact (tr0_bytes _ _ _ _ MU Q16)|].
      exact (tr0_rw _ _ _ _ MU WM C32).
    + assert (K : ukind g (uQ g p) <> PN.KFit) by (intros K; apply ures_pos in K; lia).
      rewrite (uafter_nfit g p K). apply H5.
      exists b, h, buf. split; [exact Hgood|].
      exists fx', L, A, regs', mem', md. split; [reflexivity|]. split; [exact Hfrm|]. split; [exact FR'|].
      split; [exact HP|].
      split; [exact WK'|]. split; [exact RC'|].
      split; [lia|]. split; [exact Hpn|]. split; [exact K|].
      split; [rewrite (ss_getr_eqv _ _ 21 XR); exact G21|].
      split; [rewrite (ss_getr_eqv _ _ 25 XR); rewrite G25; exact E25|].
      rewrite (ss_getr_eqv _ _ 27 XR); exact G27.
Qed.

Lemma un_le_n : forall g, un g <= g_n g.
Proof. intros g. unfold un, uF, zlen, g_n. destruct (g_in g) as [|d l]; cbn [tl length]; lia. Qed.

Lemma un_range : forall g, GV B empty g -> 0 <= un g < 2 ^ 26.
Proof. intros g (Hn & _). pose proof (un_le_n g). unfold un, zlen in *. lia. Qed.

Lemma ugood_len : forall g, ugood g = true -> 24 <= un g.
Proof.
  intros g H. unfold ugood, PS.pcap_good in H. apply andb_prop in H as [H _]. apply Z.leb_le in H. exact H.
Qed.

Lemma uswz_01 : forall g, uswz g = 0 \/ uswz g = 1.
Proof. intros g. unfold uswz, PS.pcap_sw. destruct (PS.pcap_magic (uF g) =? 0xD4C3B2A1); [right | left]; reflexivity. Qed.

(* The fields after the stream pointer in the source cells at a. *)
Lemma psc_parts : forall m a f sw o v i pad, rw_cells rsegs m a (PS.ps_cells f sw o v i pad) ->
  bytes_at rsegs m (a + 8) (le4 sw) /\ bytes_at rsegs m (a + 12) (le4 o) /\ bytes_at rsegs m (a + 16) (le4 v) /\
  bytes_at rsegs m (a + 20) (le2 i).
Proof.
  intros m a f sw o v i pad [[_ Hb] _]. unfold PS.ps_cells in Hb. cbn [cells_bytes cbytes] in Hb.
  apply bytes_at_app in Hb as [_ Hb]. rewrite length_le8 in Hb.
  apply bytes_at_app in Hb as [H1 Hb]. rewrite length_le4 in Hb.
  apply bytes_at_app in Hb as [H2 Hb]. rewrite length_le4 in Hb.
  apply bytes_at_app in Hb as [H3 Hb]. rewrite length_le4 in Hb.
  apply bytes_at_app in Hb as [H4 _].
  split; [exact H1|]. split; [replace (a + 12) with (a + Z.of_nat 8 + Z.of_nat 4) by lia; exact H2|].
  split; [replace (a + 16) with (a + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4) by lia; exact H3|].
  replace (a + 20) with (a + Z.of_nat 8 + Z.of_nat 4 + Z.of_nat 4 + Z.of_nat 4) by lia. exact H4.
Qed.

(* Cells and arrays carried by mbyte equality, with writability from the new memory. *)
Lemma tr_wr_rw : forall (m m' : word -> option byte) a cs,
  (forall i, 0 <= i < Z.of_nat (cells_size cs) ->
     writable_at rsegs m' (a + i) /\ mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  rw_cells rsegs m a cs -> rw_cells rsegs m' a cs.
Proof.
  intros m m' a cs H [[Hwf Hb] (Hw1 & Hw2 & Hw3)].
  split; [split; [exact Hwf|]|].
  - apply (tr_mb_bytes m m' a (cells_bytes cs)); [|exact Hb].
    intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf. exact (proj2 (H i Hi)).
  - split; [exact Hw1|]. split; [exact Hw2|]. intros i Hi. exact (proj1 (H i Hi)).
Qed.

Lemma tr_u8 : forall (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) ->
     writable_at rsegs m' (a + i) /\ mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  Arr.u8arr rsegs m a bs -> Arr.u8arr rsegs m' a bs.
Proof.
  intros m m' a bs H [Hb (W1 & W2 & W3)]. split.
  - apply (tr_mb_bytes m m' a bs); [|exact Hb]. intros i Hi. exact (proj2 (H i Hi)).
  - split; [exact W1|]. split; [exact W2|]. intros i Hi. exact (proj1 (H i Hi)).
Qed.

Lemma tr_errf_se : forall (m m' : word -> option byte),
  (forall x, A_STDERR <= x < A_STDERR + 232 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (exists fl md, errf m fl md) -> exists fl md, errf m' fl md.
Proof.
  intros m m' H (fl & md & E1 & E2). exists fl, md. split; [|exact E2].
  apply (tr_img_rw m m' A_STDERR _); [|exact E1].
  intros i Hi. cbn [cells_size csize stderr_cells] in Hi.
  split; [right; right; lia | apply H; lia].
Qed.

(* The slot's stack window is writable in every frame record. *)
Lemma fr_wr : forall g km hb L A regs mem md x, FR B APIf ra empty g km hb L A regs mem md ->
  g_S g - SLOT_K <= x < g_S g -> writable_at rsegs mem x.
Proof.
  intros g km hb L A regs mem md x HF Hx.
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HW).
  rewrite <- (ss_segs B APIf ra empty FF). exact (HW x Hx).
Qed.

Lemma tr_frw : forall g km hb L A regs mem md (m0 : word -> option byte) a cs,
  FR B APIf ra empty g km hb L A regs mem md -> g_S g - SLOT_K <= a -> a + Z.of_nat (cells_size cs) <= g_S g ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> mbyte rsegs mem (a + i) = mbyte rsegs m0 (a + i)) ->
  rw_cells rsegs m0 a cs -> rw_cells rsegs mem a cs.
Proof.
  intros g km hb L A regs mem md m0 a cs HF H1 H2 HE. apply tr_wr_rw. intros i Hi.
  split; [apply (fr_wr g km hb L A regs mem md); [exact HF | lia] | exact (HE i Hi)].
Qed.

Hypothesis HCLOSE : forall fx0 : YK11.FPState, @pcap_source_close_contract fx0 rc B (APIf rc).

(* W (URec.H5): K5, the walk's end at p, through the end loop to the close of the stream, then 0x1306c. *)
Lemma ug_W : Hcut_o B APIf ra (Inv_K130a4 B APIf ra empty) uC0 -> forall g p, HC5 B APIf ra empty g p.
Proof.
  intros HT g p c (b & h & buf & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPr).
  destruct HPr as (HWK & HREC & Hp & Hpn & K & E21 & E25 & E27).
  pose proof HWK as (H8 & H9 & H26 & (Hstd & Hgd & Herr & Q0 & QL) & QG & HBF & Q24).
  pose proof HREC as (HMS & HOO & (lol & lvt & lvid & pad & HPS) & HTS & (bj & HU & HL & HFT)).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (ss_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & _).
  pose proof (un_range g HGV) as HN.
  pose proof (@YM05.alloc_ceiling_lt rc) as HAC.
  destruct (ss_hb_blk B APIf ra empty FF g 3 _ L A regs mem md b (un g) HF HP
    ltac:(unfold HB3; cbn [In]; left; reflexivity)) as (_ & Hb1 & Hb2 & _).
  assert (USP : bv_unsigned (getr regs 2) = fsp g)
    by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
  assert (HE : 0 <= p <= PN.flen (uF g)) by (unfold PN.flen; unfold un, zlen in Hpn; lia).
  assert (HFn : bytes_at rsegs (normalize rsegs mem) b (uF g)) by (apply bytes_at_normalize; [exact HMI | exact HBF]).
  assert (Q0n : bytes_at rsegs (normalize rsegs mem) (fsp g) (le8 (wz (ud g)))).
  { apply bytes_at_normalize; [exact HMI|]. unfold q64, spk in Q0. rewrite Z.add_0_r in Q0. exact Q0. }
  assert (QLn : bytes_at rsegs (normalize rsegs mem) (symaddr Symbols.Ubsan.s_g_file_len) (le8 (wz (PN.flen (uF g)))))
    by (apply bytes_at_normalize; [exact HMI | exact QL]).
  assert (Q56n : bytes_at rsegs (normalize rsegs mem) (fsp g + 56) (le4 (wz (uswz g)))).
  { apply bytes_at_normalize; [exact HMI|]. destruct (psc_parts _ _ _ _ _ _ _ _ HPS) as (S1 & _).
    unfold spk in S1. replace (fsp g + 56) with (fsp g + 48 + 8) by lia. exact S1. }
  pose proof (proj1 (PW.kind_nfit (usw g) (uF g) (ucap g) (uQ g p) K)) as EA.
  set (Q := fun (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) =>
    m' = normalize rsegs mem /\ pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_close) /\ getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z) /\
    getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
    getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 10 = wz (fsp g + 48) /\
    getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27).
  apply (ss_kA_run_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x400)%Z)) mem md Q (uC0 g) (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (ss_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of.
    eapply evt_mono; [exact (ubs_W_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (uF g) (usw g) (fsp g) (ures g (uQ g p)) p (uQ g p) (ucap g) (ud g) b (uswz g)
      rd32f_holds USP E21 EA K E25 HE (PW.psn_q_skips (usw g) (uF g) (ucap g) p ltac:(lia)) H8 ltac:(lia)
      ltac:(unfold PN.flen; unfold un, zlen in Hb2; lia) HFn H9 eq_refl (ud_range g) Q0n H26 QLn Q56n
      (uswz_01 g) eq_refl ltac:(unfold PN.flen; unfold un, zlen in HN; lia))|].
    intros ms (a1' & a2' & a3' & a4' & a5' & s2' & s3' & s4' & s9' & ->).
    do 3 eexists. split; [reflexivity|]. repeat split; reflexivity.
  - intros R pc' m' regs' mem' (-> & -> & G1 & G2 & G3 & G4 & G8 & G9 & G10 & G26 & G27) XR HR HS.
    destruct (ug_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 3 (HB3 g b h buf) L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
        | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM | intros lo hi y [] ]. }
    assert (K1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
    assert (K8 : getr regs' 8 = getr regs 8) by (rewrite (ss_getr_eqv _ _ 8 XR); exact G8).
    assert (K9 : getr regs' 9 = getr regs 9) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
    assert (K10 : getr regs' 10 = wz (spk g 48)) by (rewrite (ss_getr_eqv _ _ 10 XR); exact G10).
    assert (K26 : getr regs' 26 = getr regs 26) by (rewrite (ss_getr_eqv _ _ 26 XR); exact G26).
    assert (K27 : getr regs' 27 = getr regs 27) by (rewrite (ss_getr_eqv _ _ 27 XR); exact G27).
    pose proof (tr0_WKEEP g b buf regs regs' mem mem' MU WM K8 K9 K26 HWK) as WK'.
    pose proof WK' as (H8' & H9' & H26' & (Hstd' & Hgd' & Herr' & Q0' & QL') & QG' & HBF' & Q24').
    pose proof (tr0_rw _ _ _ _ MU WM HPS) as HPS'.
    pose proof (mstl_transport [] mem mem' h b (uF g) _ _ _ HMS MU WM I I) as HMS'.
    pose proof (tr0_rw _ _ _ _ MU WM HOO) as HOO'.
    pose proof (Arr.u8arr_transport rsegs [] mem mem' buf bj HU MU WM I) as HU'.
    eapply (ps_close_step B APIf ra empty FF (HCLOSE _) g 3 [(b, un g)] h [(buf, ubn g)] L A regs' mem' md
      (spk g 48) (wz (uswz g)) _ _ _ pad b (uF g) (upos g (uQ g p)) (uC0 g) (Post_o B APIf ra g) FR' HP).
    + rewrite K1. apply ug_ret_ok; lia.
    + exact K10.
    + unfold spk; lia.
    + unfold spk, fsp, SLOT_FRAME; lia.
    + unfold spk. Z.div_mod_to_equations. lia.
    + exact HPS'.
    + cbn [app In]. left. reflexivity.
    + exact HMS'.
    + exact HOO'.
    + exact Hstd'.
    + intros L2 A2 regs2 mem2 md2 HF2 HP2 RP2 KF KB KI HPS2 HOE2 HSTD2 HGU2 HBF2.
      rewrite (ss_segs B APIf ra empty FF) in KF, KB, KI.
      rewrite K1. apply HT. exists b, buf. split; [exact Hgood|].
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z) 3 [(b, un g); (buf, ubn g)] _ L2 A2 regs2 mem2 md2 Hfrm HF2
        HP2).
      split; [split; [|split]|split].
      * split; [transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia)) | exact H8']|].
        split; [transitivity (getr regs' 9); [exact (RP2 9 ltac:(unfold callee_saved; lia)) | exact H9']|].
        split; [transitivity (getr regs' 26); [exact (RP2 26 ltac:(unfold callee_saved; lia)) | exact H26']|].
        split.
        { split; [exact HSTD2|]. split; [exact HGU2|]. split.
          - apply (tr_errf_se mem' mem2); [|exact Herr']. intros x Hx.
            apply KI; [right; right; exact Hx | unfold A_STDERR, A_OFL_HEAD in *; lia].
          - split.
            + apply (tr_mb_bytes mem' mem2 _ _); [|exact Q0']. intros i Hi. rewrite length_le8 in Hi.
              apply KF; unfold spk, fsp, SLOT_FRAME in *; lia.
            + apply (tr_mb_bytes mem' mem2 _ _); [|exact QL']. intros i Hi. rewrite length_le8 in Hi.
              apply KI; [apply img_w_iff; right; left; unfold G_FILE_LEN in *; lia
                        | unfold G_FILE_LEN, A_OFL_HEAD in *; lia]. }
        split.
        { apply (tr_mb_bytes mem' mem2 _ _); [|exact QG']. intros i Hi. rewrite length_le8 in Hi.
          apply KI; [apply img_w_iff; right; left; unfold G_FILE_LEN in *; lia | unfold G_FILE_LEN, A_OFL_HEAD in *; lia]. }
        split; [exact HBF2|].
        apply (tr_mb_bytes mem' mem2 _ _); [|exact Q24']. intros i Hi. rewrite length_le8 in Hi.
        apply KF; unfold spk, fsp, SLOT_FRAME in *; lia.
      * transitivity (getr regs' 27); [exact (RP2 27 ltac:(unfold callee_saved; lia))|]. rewrite K27. exact E27.
      * exists bj. split; [|exact HL].
        destruct (ss_hb_blk B APIf ra empty FF g 3 _ L2 A2 regs2 mem2 md2 buf (ubn g) HF2 HP2
          ltac:(cbn [app In]; right; left; reflexivity)) as (W & _).
        rewrite (ss_segs B APIf ra empty FF) in W.
        apply (tr_u8 mem' mem2 buf bj); [|exact HU']. intros i Hi. rewrite HL in Hi.
        split; [exact (proj1 (W i Hi)) | apply (KB buf (ubn g) i); [cbn [app In]; right; left; reflexivity | exact Hi]].
      * exact HOE2.
      * do 3 eexists. exists pad. exact HPS2.
Qed.

(* An 8-byte cell of the stack window. *)
Lemma c8_of_stk : forall m lo hi a, stk rsegs m lo hi -> lo <= a -> a + 8 <= hi -> exists v, rw_cells rsegs m a [C8 v].
Proof.
  intros m lo hi a ST H1 H2. destruct (ss_rw_of_stk m lo hi a 8 ST H1 ltac:(lia)) as (bs & [[[Hl _] Hb] Hw]).
  destruct (U.Prog.memmove.le8_surj bs Hl) as (v & ->).
  exists v. split; [split; [split; exact I | exact Hb] | exact Hw].
Qed.

(* From the normalized memory of a run to the actual one. *)
Lemma rw_rel : forall (m m0 : word -> option byte) a cs, mem_rel rsegs m m0 -> rw_cells rsegs m0 a cs ->
  rw_cells rsegs m a cs.
Proof.
  intros m m0 a cs HR [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (proj2 (bytes_at_rel rsegs m m0 a _ HR) Hb)] | exact (wr_at_rel rsegs m m0 a _ HR Hw)].
Qed.

Lemma q64_of_rw : forall m a v, rw_cells rsegs m a [C8 (wz v)] -> q64 m a v.
Proof.
  intros m a v H. pose proof (ss_cells_bytes m a _ H) as Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  exact Hb.
Qed.

(* Writes inside two intervals miss every range wholly below, between or above them. *)
Lemma disj_W : forall W a n lo1 hi1 lo2 hi2,
  (forall lo hi, In (lo, hi) W -> (lo1 <= lo /\ hi <= hi1) \/ (lo2 <= lo /\ hi <= hi2)) ->
  lo1 <= hi1 <= lo2 /\ lo2 <= hi2 ->
  (a + n <= lo1 \/ (hi1 <= a /\ a + n <= lo2) \/ hi2 <= a) -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n lo1 hi1 lo2 hi2 HW Ho Ha; cbn [disjoint_from]; [exact I|].
  split; [destruct (HW lo hi (or_introl eq_refl)); lia|].
  apply (IH a n lo1 hi1 lo2 hi2); [intros lo' hi' Hin; exact (HW lo' hi' (or_intror Hin)) | exact Ho | exact Ha].
Qed.

Ltac dj := rewrite ?length_le8, ?length_le4; cbn [length cells_size csize stderr_cells PS.ps_cells];
  unfold A_LIBC, A_OFL_LOCK, A_GOT_GUARD, A_GUARD, A_STDERR, A_OFL_HEAD, G_FILE_LEN, spk; lia.

(* WKEEP across writes in the frame cells sp_h + 8 .. + 24 and sp_h + 32 .. + 48. *)
Lemma trW_WKEEP : forall g b buf regs regs' m m' W, munch W m m' -> wmono rsegs m m' ->
  (forall lo hi, In (lo, hi) W -> (fsp g + 8 <= lo /\ hi <= fsp g + 24) \/ (fsp g + 32 <= lo /\ hi <= fsp g + 48)) ->
  (symaddr ImgPages.Ubsan.top) <= fsp g -> b + un g <= fsp g ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 26 = getr regs 26 ->
  WKEEP g b buf regs m -> WKEEP g b buf regs' m'.
Proof.
  intros g b buf regs regs' m m' W MU WM HW Hf Hb E8 E9 E26
    (H8 & H9 & H26 & ((S1 & S2 & S3) & (G1 & gv & G2) & (fl & md & (E1 & E2)) & Q0 & QL) & Q8 & HB & Q24).
  assert (Ho : fsp g + 8 <= fsp g + 24 <= fsp g + 32 /\ fsp g + 32 <= fsp g + 48) by lia.
  pose proof (fun a n => disj_W W a n _ _ _ _ HW Ho) as D. unfold un, zlen in Hb.
  split; [rewrite E8; exact H8|]. split; [rewrite E9; exact H9|]. split; [rewrite E26; exact H26|].
  split.
  { split; [split; [|split]|split; [split|split; [|split]]].
    - eapply bytes_at_transport; [exact S1 | exact MU | apply D; dj].
    - eapply bytes_at_transport; [exact S2 | exact MU | apply D; dj].
    - eapply bytes_at_transport; [exact S3 | exact MU | apply D; dj].
    - eapply bytes_at_transport; [exact G1 | exact MU | apply D; dj].
    - exists gv. eapply bytes_at_transport; [exact G2 | exact MU | apply D; dj].
    - exists fl, md. split; [|exact E2]. eapply rw_cells_transport; [exact E1 | exact MU | exact WM | apply D; dj].
    - eapply bytes_at_transport; [exact Q0 | exact MU | apply D; dj].
    - eapply bytes_at_transport; [exact QL | exact MU | apply D; dj]. }
  split; [eapply bytes_at_transport; [exact Q8 | exact MU | apply D; dj]|].
  split; [eapply bytes_at_transport; [exact HB | exact MU | apply D; dj]|].
  eapply bytes_at_transport; [exact Q24 | exact MU | apply D; dj].
Qed.

(* RECST across writes in the frame cells sp_h + 8 .. + 24 and sp_h + 32 .. + 40. *)
Lemma trW_RECST : forall g b h buf p m m' W, munch W m m' -> wmono rsegs m m' ->
  (forall lo hi, In (lo, hi) W -> (fsp g + 8 <= lo /\ hi <= fsp g + 24) \/ (fsp g + 32 <= lo /\ hi <= fsp g + 40)) ->
  (symaddr ImgPages.Ubsan.top) <= fsp g -> b + un g <= fsp g -> h + 1304 <= fsp g -> buf + ubn g <= fsp g ->
  RECST g b h buf p m -> RECST g b h buf p m'.
Proof.
  intros g b h buf p m m' W MU WM HW Hf Hb Hh Hbuf (HS & HO & (lol & lvt & lvid & pad & HP) & HT & (bj & HU & HL & HF)).
  assert (Ho : fsp g + 8 <= fsp g + 24 <= fsp g + 32 /\ fsp g + 32 <= fsp g + 40) by lia.
  pose proof (fun a n => disj_W W a n _ _ _ _ HW Ho) as D. unfold un, zlen in Hb.
  split; [eapply mstl_transport; [exact HS | exact MU | exact WM | apply D; lia | apply D; lia]|].
  split; [eapply rw_cells_transport; [exact HO | exact MU | exact WM | apply D; dj]|].
  split; [exists lol, lvt, lvid, pad; eapply rw_cells_transport; [exact HP | exact MU | exact WM | apply D; dj]|].
  split; [eapply rw_cells_transport; [exact HT | exact MU | exact WM | apply D; dj]|].
  exists bj. split; [|split; [exact HL | exact HF]].
  eapply Arr.u8arr_transport; [exact HU | exact MU | exact WM | apply D; lia].
Qed.

(* The frame and the three heap blocks of the walk lie apart: the blocks below the stack window, below the frame.
   fx0 instantiates the FP state of the frame-record lemmas, whose statements do not depend on it. *)
Lemma hb3_bnd : forall (fx0 : YK11.FPState) g b h buf km L A regs mem md,
  FR B APIf ra empty g km (HB3 g b h buf) L A regs mem md ->
  Permutation (blocks L A) (HB3 g b h buf ++ blocks (g_L g) (g_A g)) ->
  (symaddr ImgPages.Ubsan.top) <= fsp g /\ 4096 <= b /\ b + un g <= fsp g /\ 4096 <= h /\ h + 1304 <= fsp g /\
  4096 <= buf /\ buf + ubn g <= fsp g /\ fsp g + 176 = g_S g /\ g_S g <= 2 ^ 47 /\ fsp g mod 16 = 0 /\
  SLOT_K = 65536 /\ alloc_ceiling + SLOT_K <= g_S g /\ b + un g <= alloc_ceiling /\
  h + 1304 <= alloc_ceiling /\ buf + ubn g <= alloc_ceiling /\ bv_unsigned (getr regs 2) = fsp g.
Proof.
  intros fx0 g b h buf km L A regs mem md HF HP.
  pose proof (ss_stk_fsp B APIf ra empty g km _ L A regs mem md HF) as (_ & HI & _ & Hf & HAC & HS47 & HK & HSP).
  pose proof (ss_fr_bnd B APIf ra empty FF g km _ L A regs mem md HF) as (_ & H16 & _).
  destruct (ss_hb_blk B APIf ra empty FF g km _ L A regs mem md b (un g) HF HP
    ltac:(unfold HB3; cbn [In]; left; reflexivity)) as (_ & B1 & B2 & _).
  destruct (ss_hb_blk B APIf ra empty FF g km _ L A regs mem md h 1304 HF HP
    ltac:(unfold HB3; cbn [In]; right; left; reflexivity)) as (_ & C1 & C2 & _).
  destruct (ss_hb_blk B APIf ra empty FF g km _ L A regs mem md buf (ubn g) HF HP
    ltac:(unfold HB3; cbn [In]; right; right; left; reflexivity)) as (_ & D1 & D2 & _).
  unfold IMG_HI in HI.
  assert (USP : bv_unsigned (getr regs 2) = fsp g) by (rewrite HSP; apply unsigned_lit; lia).
  repeat split; try assumption; lia.
Qed.

(* D: 0x12e04, the first call answered with ufirst, to K4 (index 0, position 24) or K5 (position 24). *)
Lemma ug_D : forall g, (forall p, HC5 B APIf ra empty g p) -> (forall i p, HC4 B APIf ra empty g i p) ->
  forall c, Inv_K12e3c B APIf ra empty g c -> SRO (ms_segs B) c (uafter g 24) (Post_o B APIf ra g).
Proof.
  intros g H5 H4 c (b & h & buf & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPr).
  destruct HPr as (E10 & E18 & HWK & HREC).
  pose proof HWK as (H8 & _).
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (ss_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (hb3_bnd fx' g b h buf 3 L A regs mem md HF HP)
    as (Hf & Hb0 & Hb & Hh0 & Hhb & Hbuf0 & Hbuf & Hfsp & HS47 & H16 & HK & HAC & _ & _ & _ & USP).
  pose proof (ss_fr_stk B APIf ra empty FF g _ _ L A regs mem md HF) as HST.
  assert (HST' : stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (fsp g + 176)) by (rewrite Hfsp; exact HST).
  destruct (c8_of_stk _ _ _ (fsp g + 8) HST ltac:(lia) ltac:(lia)) as (v8 & R8).
  destruct (c8_of_stk _ _ _ (fsp g + 16) HST ltac:(lia) ltac:(lia)) as (v16 & R16).
  destruct (c8_of_stk _ _ _ (fsp g + 32) HST ltac:(lia) ltac:(lia)) as (v32 & R32).
  set (W := [(fsp g + 8, fsp g + 24); (fsp g + 32, fsp g + 40)]).
  set (Q := fun (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) =>
    ((0 < ufirst g /\ pc' = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1ec)%Z) /\ munch W (normalize rsegs mem) m' /\
      wmono rsegs (normalize rsegs mem) m' /\ rw_cells rsegs m' (fsp g + 8) [C8 (wz (buf + 12))] /\
      rw_cells rsegs m' (fsp g + 16) [C8 (wz (1000000 * 2 ^ 32))] /\ rw_cells rsegs m' (fsp g + 32) [C8 (wz 0)] /\
      getr R 18 = wz (-8) /\ getr R 20 = bv_not (wz b)) \/
     (ufirst g <= 0 /\ pc' = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x400)%Z) /\ m' = normalize rsegs mem)) /\
    getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = wz b /\
    getr R 9 = getr regs 9 /\ getr R 21 = wz (ufirst g) /\ getr R 25 = wz 24 /\ getr R 26 = getr regs 26 /\
    getr R 27 = wz (ufirst g)).
  apply (ss_kA_run_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z)) mem md Q (uafter g 24) (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (ss_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of.
    eapply evt_mono; [exact (ubs_D_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (g_S g - SLOT_K) (fsp g) (ufirst g) b buf v8 v16 v32 USP E10 (ures_range g (uQ g 24))
      H8 E18 R8 R16 R32 (mem_inv_normalize rsegs mem) HST')|].
    intros ms [(P & m1 & -> & MU0 & WM0 & _ & _ & D8 & D16 & D32) | (P & ->)];
      do 3 eexists; (split; [reflexivity|]).
    + split; [left; split; [exact P|]; split; [reflexivity|]; split; [exact MU0|]; split; [exact WM0|];
        split; [exact D8|]; split; [exact D16|]; split; [exact D32|]; split; reflexivity|].
      repeat split; reflexivity.
    + split; [right; split; [exact P|]; split; reflexivity|]. repeat split; reflexivity.
  - intros R pc' m' regs' mem' ([(P & -> & MU0 & WM0 & D8 & D16 & D32 & G18 & G20) | (P & -> & ->)] &
      G2 & G3 & G4 & G8 & G9 & G21 & G25 & G26 & G27) XR HR HS.
    + pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
      pose proof (munch_rel rsegs W mem _ mem' _ HR0 HR HS MU0) as MU.
      pose proof (wmono_rel rsegs mem _ mem' _ HR0 HR HS WM0) as WM.
      assert (FR' : FR B APIf ra empty g 3 (HB3 g b h buf) L A regs' mem' md).
      { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' W HF HP);
          [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
          | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM |].
        intros lo hi y Hin Hy. left. unfold W in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
      assert (K8 : getr regs' 8 = getr regs 8) by (rewrite (ss_getr_eqv _ _ 8 XR), G8; symmetry; exact H8).
      assert (K9 : getr regs' 9 = getr regs 9) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
      assert (K26 : getr regs' 26 = getr regs 26) by (rewrite (ss_getr_eqv _ _ 26 XR); exact G26).
      pose proof (trW_WKEEP g b buf regs regs' mem mem' W MU WM
        ltac:(intros lo hi Hin; unfold W in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-; lia)
        Hf Hb K8 K9 K26 HWK) as WK'.
      pose proof (trW_RECST g b h buf 24 mem mem' W MU WM
        ltac:(intros lo hi Hin; unfold W in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-; lia)
        Hf Hb Hhb Hbuf HREC) as RC'.
      assert (K : ukind g (uQ g 24) = PN.KFit) by (apply ures_pos; exact P).
      rewrite (uafter_fit g 24 K). apply (H4 0 24).
      exists b, h, buf, (getr regs' 13). split; [exact Hgood|].
      exists fx', L, A, regs', mem', md. split; [reflexivity|]. split; [exact Hfrm|]. split; [exact FR'|].
      split; [exact HP|].
      split; [exact WK'|]. split; [exact RC'|].
      split; [lia|]. split; [lia|]. split; [exact K|].
      split; [rewrite (ss_getr_eqv _ _ 18 XR); exact G18|].
      split; [rewrite (ss_getr_eqv _ _ 20 XR); exact G20|].
      split; [rewrite (ss_getr_eqv _ _ 21 XR); exact G21|].
      split; [rewrite (ss_getr_eqv _ _ 25 XR); exact G25|].
      split; [rewrite (ss_getr_eqv _ _ 27 XR); exact G27|].
      split; [reflexivity|].
      split; [left; split; reflexivity|].
      split; [exact (q64_of_rw _ _ _ (rw_rel _ _ _ _ HR D8))|].
      split; [exact (q64_of_rw _ _ _ (rw_rel _ _ _ _ HR D16))|].
      exact (rw_rel _ _ _ _ HR D32).
    + destruct (ug_same mem mem' HMI HR HS) as (MU & WM).
      assert (FR' : FR B APIf ra empty g 3 (HB3 g b h buf) L A regs' mem' md).
      { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' [] HF HP);
          [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
          | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM | intros lo hi y [] ]. }
      assert (K8 : getr regs' 8 = getr regs 8) by (rewrite (ss_getr_eqv _ _ 8 XR), G8; symmetry; exact H8).
      assert (K9 : getr regs' 9 = getr regs 9) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
      assert (K26 : getr regs' 26 = getr regs 26) by (rewrite (ss_getr_eqv _ _ 26 XR); exact G26).
      pose proof (tr0_WKEEP g b buf regs regs' mem mem' MU WM K8 K9 K26 HWK) as WK'.
      pose proof (tr0_RECST g b h buf 24 mem mem' MU WM HREC) as RC'.
      assert (K : ukind g (uQ g 24) <> PN.KFit) by (intros K; apply ures_pos in K; unfold ufirst in P; lia).
      rewrite (uafter_nfit g 24 K). apply (H5 24).
      exists b, h, buf. split; [exact Hgood|].
      exists fx', L, A, regs', mem', md. split; [reflexivity|]. split; [exact Hfrm|]. split; [exact FR'|].
      split; [exact HP|].
      split; [exact WK'|]. split; [exact RC'|].
      split; [lia|]. split; [exact (ugood_len g Hgood)|]. split; [exact K|].
      split; [rewrite (ss_getr_eqv _ _ 21 XR); exact G21|].
      split; [rewrite (ss_getr_eqv _ _ 25 XR); exact G25|].
      rewrite (ss_getr_eqv _ _ 27 XR); exact G27.
Qed.

Lemma rw_norm : forall m a cs, ro_agree rsegs m -> IMG_HI <= a -> a + Z.of_nat (cells_size cs) <= 2 ^ 64 ->
  rw_cells rsegs m a cs -> rw_cells rsegs (normalize rsegs m) a cs.
Proof.
  intros m a cs HRO Ha Hn [[Hwf Hb] Hw].
  split; [split; [exact Hwf | exact (bytes_at_normalize rsegs m a _ HRO Hb)] | exact (ss_wr_norm m a _ Ha Hn Hw)].
Qed.

Lemma u8_prefix : forall m a bj k l, Arr.u8arr rsegs m a bj -> firstn k bj = l -> bytes_at rsegs m a l.
Proof.
  intros m a bj k l [Hb _] <-. rewrite <- (firstn_skipn k bj) in Hb. apply bytes_at_app in Hb as [H _]. exact H.
Qed.

Lemma mstl_bytes : forall m h b F p pv nx, mstl m h b F p pv nx ->
  bytes_at rsegs m b F /\ (h + 1304 <= b \/ b + Z.of_nat (length F) <= h).
Proof. intros m h b F p pv nx (fl & md & q & rb & (buf & _ & _ & _ & HB & _ & HD) & _). split; [exact HB | exact HD]. Qed.

Hypothesis BC : bcmp_contract.
Hypothesis HNEXT : forall fx0 : YK11.FPState, @pcap_source_next_contract fx0.

(* L (URec.HL): K4 at index i and position p (the fit record uQ g p) through the record checks to the call of
   pcap_source_next from p1 = upos g (uQ g p) with ts = sp_h + 40, then 0x13034 at index i + 1 and position p1. *)
Lemma ug_L : forall g i p, HC6 B APIf ra empty g (i + 1) (upos g (uQ g p)) ->
  forall c, Inv_K4 B APIf ra empty g i p c ->
    SRO (ms_segs B) c (uout1 g (upos g (uQ g p)) ++ uafter g (upos g (uQ g p))) (Post_o B APIf ra g).
Proof.
  intros g i p H6 c (b & h & buf & a3 & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPr).
  destruct HPr as (HWK & HREC & Hi & Hp & K & E18 & E20 & E21 & E25 & E27 & E13 & HI & Q8 & Q16 & C32).
  pose proof HWK as (H8 & H9 & H26 & (Hstd & Hgd & Herr & Q0 & QL) & QG & HBF & Q24).
  pose proof HREC as (HMS & HOO & (lol & lvt & lvid & pad & HPS) & HTS & (bj & HU & HL & HFT)).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (ss_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (hb3_bnd fx' g b h buf 3 L A regs mem md HF HP)
    as (Hf & Hb0 & Hb & Hh0 & Hhb & Hbuf0 & Hbuf & Hfsp & HS47 & H16 & HK & HAC & Hbc & Hhc & Hbufc & USP).
  pose proof (un_range g HGV) as HN. pose proof (ugood_len g Hgood) as H24.
  pose proof (ucap_range g) as HC.
  pose proof (@YM05.alloc_ceiling_lt rc) as HACL.
  pose proof (ss_fr_stk B APIf ra empty FF g _ _ L A regs mem md HF) as HST.
  assert (HST' : stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (fsp g + 176)) by (rewrite Hfsp; exact HST).
  destruct (PW.kind_fit (usw g) (uF g) (ucap g) (uQ g p) K) as (KR & KL & KP & KE & KIc).
  assert (EP : upos g (uQ g p) = uQ g p + 16 + PN.incl (usw g) (uF g) (uQ g p)) by exact KP.
  destruct (upos_fit g p ltac:(lia) K) as (Hp1 & Hp1n).
  pose proof (PW.walk_pos_step (usw g) (uF g) (ucap g) p i Hp K) as Hpi.
  (* The facts of the segment, on the normalized memory. *)
  assert (E21' : getr regs 21 = wz (PN.rec_len (usw g) (uF g) (uQ g p))) by (rewrite E21; unfold ures; rewrite KR; reflexivity).
  assert (HI' : (i = 0 /\ ufirst g = PN.rec_len (usw g) (uF g) (uQ g p)) \/ (0 < i /\ getr regs 13 = wz (ufirst g))).
  { destruct HI as [(-> & ->) | (Hi0 & Ea)];
      [left; split; [reflexivity | unfold ufirst, ures; exact KR] | right; split; [exact Hi0 | rewrite E13; exact Ea]]. }
  assert (HFn : bytes_at rsegs (normalize rsegs mem) b (uF g)) by (apply bytes_at_normalize; [exact HMI | exact HBF]).
  pose proof (bytes_at_normalize rsegs mem _ _ HMI QL) as QLn.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI Q8) as Q8n.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI Q16) as Q16n.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI Q24) as Q24n.
  assert (C32n : rw_cells rsegs (normalize rsegs mem) (spk g 32) [C8 (wz i)])
    by (apply rw_norm; [exact HMI | unfold IMG_HI, spk; lia | unfold spk; cbn [cells_size csize]; lia | exact C32]).
  rewrite (PW.ts_of_fit (usw g) (uF g) (ucap g) (uQ g p) (wz (-1)) K) in HTS.
  assert (TSn : rw_cells rsegs (normalize rsegs mem) (spk g 40) [C8 (wz (PN.rec_ts (usw g) (uF g) (uQ g p)))])
    by (apply rw_norm; [exact HMI | unfold IMG_HI, spk; lia | unfold spk; cbn [cells_size csize]; lia | exact HTS]).
  destruct (psc_parts _ _ _ _ _ _ _ _ HPS) as (S1 & S2 & S3 & S4). unfold spk in S1, S2, S3, S4.
  rewrite (PW.lol_of_fit (usw g) (uF g) (ucap g) p lol ltac:(lia) K) in S2.
  rewrite (PW.vt_of_fit (usw g) (uF g) (ucap g) (uQ g p) lvt K) in S3.
  rewrite (PW.vid_of_fit (usw g) (uF g) (ucap g) (uQ g p) lvid K) in S4.
  assert (S1n : bytes_at rsegs (normalize rsegs mem) (fsp g + 56) (le4 (wz (uswz g)))).
  { apply bytes_at_normalize; [exact HMI|]. replace (fsp g + 56) with (fsp g + 48 + 8) by lia. exact S1. }
  assert (S2n : bytes_at rsegs (normalize rsegs mem) (fsp g + 60) (le4 (wz (PN.orig (usw g) (uF g) (uQ g p))))).
  { apply bytes_at_normalize; [exact HMI|]. replace (fsp g + 60) with (fsp g + 48 + 12) by lia. exact S2. }
  assert (S3n : bytes_at rsegs (normalize rsegs mem) (fsp g + 64)
    (le4 (wz (if PN.tagged (usw g) (uF g) (uQ g p) then 1 else 0)))).
  { apply bytes_at_normalize; [exact HMI|]. replace (fsp g + 64) with (fsp g + 48 + 16) by lia.
    revert S3. destruct (PN.tagged (usw g) (uF g) (uQ g p)); intros S3; exact S3. }
  assert (S4n : bytes_at rsegs (normalize rsegs mem) (fsp g + 68)
    (le2 (wz (if PN.tagged (usw g) (uF g) (uQ g p) then PN.rec_vid (uF g) (uQ g p) else 0)))).
  { apply bytes_at_normalize; [exact HMI|]. replace (fsp g + 68) with (fsp g + 48 + 20) by lia.
    revert S4. destruct (PN.tagged (usw g) (uF g) (uQ g p)); intros S4; exact S4. }
  assert (HBUFn : bytes_at rsegs (normalize rsegs mem) buf (PN.rec_bytes (usw g) (uF g) (uQ g p))).
  { apply bytes_at_normalize; [exact HMI|]. exact (u8_prefix mem buf bj _ _ HU (HFT ltac:(rewrite K; reflexivity))). }
  set (Qn := uQ g p + 16 + PN.incl (usw g) (uF g) (uQ g p)).
  set (Q := fun (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) =>
    pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next) /\ munch [(fsp g + 32, fsp g + 48)] (normalize rsegs mem) m' /\
    wmono rsegs (normalize rsegs mem) m' /\ rw_cells rsegs m' (fsp g + 32) [C8 (wz (i + 1))] /\
    rw_cells rsegs m' (fsp g + 40) [C8 (wz (-1))] /\
    getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z) /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
    getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 10 = wz (fsp g + 48) /\ getr R 11 = wz buf /\
    getr R 12 = wz (ucap g) /\ getr R 13 = wz (fsp g + 40) /\ getr R 18 = getr regs 18 /\
    getr R 20 = getr regs 20 /\ getr R 25 = wz Qn /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27).
  apply (ss_kA_run_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1ec)%Z)) mem md Q _ (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (ss_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of.
    eapply evt_mono; [exact (ubs_L_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (uF g) (usw g) (g_S g - SLOT_K) (fsp g) b buf (ucap g) (uswz g) i p (uQ g p) (ufirst g)
      rd32f_holds BC USP E25 H8 H9 E18 E20 E21' H26 E27 HI' Hi Hp
      (PW.psn_q_skips (usw g) (uF g) (ucap g) p ltac:(lia)) K ltac:(unfold un, zlen in HN; lia) ltac:(lia)
      ltac:(unfold un, zlen in Hb; lia) QLn HFn HC Q8n Q16n Q24n C32n TSn S1n (uswz_01 g) eq_refl S2n S3n S4n
      HBUFn Hbuf0 ltac:(unfold ubn in Hbufc; lia) ltac:(left; unfold un, zlen in Hb; lia)
      ltac:(left; unfold ubn in Hbufc; lia) ltac:(lia) (mem_inv_normalize rsegs mem) HST')|].
    intros ms (t0' & t1' & t2' & a4' & a5' & a6' & a7' & s3' & s5' & s6' & s7' & s8' & t3' & t4' & t5' & t6' & m1 & ->
      & MU0 & WM0 & _ & _ & D32 & D40).
    do 3 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [exact D32|]. split; [exact D40|].
    repeat split; reflexivity.
  - intros R pc' m' regs' mem' (-> & MU0 & WM0 & D32 & D40 & G1 & G2 & G3 & G4 & G8 & G9 & G10 & G11 & G12 & G13 &
      G18 & G20 & G25 & G26 & G27) XR HR HS.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    set (W := [(fsp g + 32, fsp g + 48)]) in MU0.
    pose proof (munch_rel rsegs W mem _ mem' _ HR0 HR HS MU0) as MU.
    pose proof (wmono_rel rsegs mem _ mem' _ HR0 HR HS WM0) as WM.
    assert (FR' : FR B APIf ra empty g 3 (HB3 g b h buf) L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' W HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
        | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM |].
      intros lo hi y Hin Hy. left. unfold W in Hin. destruct Hin as [E|[]]; injection E as <- <-; lia. }
    assert (K1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
    assert (K8 : getr regs' 8 = getr regs 8) by (rewrite (ss_getr_eqv _ _ 8 XR); exact G8).
    assert (K9 : getr regs' 9 = getr regs 9) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
    assert (K10 : getr regs' 10 = wz (spk g 48)) by (rewrite (ss_getr_eqv _ _ 10 XR); exact G10).
    assert (K11 : getr regs' 11 = wz buf) by (rewrite (ss_getr_eqv _ _ 11 XR); exact G11).
    assert (K12 : getr regs' 12 = wz (ucap g)) by (rewrite (ss_getr_eqv _ _ 12 XR); exact G12).
    assert (K13 : getr regs' 13 = wz (spk g 40)) by (rewrite (ss_getr_eqv _ _ 13 XR); exact G13).
    assert (K18 : getr regs' 18 = wz (-8)) by (rewrite (ss_getr_eqv _ _ 18 XR), G18; exact E18).
    assert (K20 : getr regs' 20 = bv_not (wz b)) by (rewrite (ss_getr_eqv _ _ 20 XR), G20; exact E20).
    assert (K25 : getr regs' 25 = wz (upos g (uQ g p))) by (rewrite (ss_getr_eqv _ _ 25 XR), G25, EP; reflexivity).
    assert (K26 : getr regs' 26 = getr regs 26) by (rewrite (ss_getr_eqv _ _ 26 XR); exact G26).
    assert (K27 : getr regs' 27 = wz (ufirst g)) by (rewrite (ss_getr_eqv _ _ 27 XR), G27; exact E27).
    pose proof (trW_WKEEP g b buf regs regs' mem mem' W MU WM
      ltac:(intros lo hi Hin; unfold W in Hin; destruct Hin as [E|[]]; injection E as <- <-; lia)
      Hf Hb K8 K9 K26 HWK) as WK'.
    pose proof WK' as (H8' & H9' & H26' & (Hstd' & Hgd' & (fl & mdv & HEF') & Q0' & QL') & QG' & HBF' & Q24').
    assert (D : forall a n, (a + n <= fsp g + 32 \/ fsp g + 48 <= a) -> disjoint_from W a n).
    { intros a n Ha. unfold W. cbn [disjoint_from]. split; [lia | exact I]. }
    pose proof (mstl_transport W mem mem' h b (uF g) _ _ _ HMS MU WM (D h 1304 ltac:(lia))
      (D b (Z.of_nat (length (uF g))) ltac:(unfold un, zlen in Hb; lia))) as HMS'.
    assert (HOO' : ofl_one mem' h).
    { eapply rw_cells_transport; [exact HOO | exact MU | exact WM | apply D; dj]. }
    assert (HPS' : rw_cells rsegs mem' (spk g 48) (PS.ps_cells (wz h) (wz (uswz g))
      (PN.lol_of (usw g) (uF g) (PN.psn_lh (usw g) (uF g) (ucap g) p) lol)
      (PN.vt_of (usw g) (uF g) (ucap g) (uQ g p) lvt) (PN.vid_of (usw g) (uF g) (ucap g) (uQ g p) lvid) pad)).
    { eapply rw_cells_transport; [exact HPS | exact MU | exact WM | apply D; dj]. }
    pose proof (Arr.u8arr_transport rsegs W mem mem' buf bj HU MU WM
      (D buf (Z.of_nat (length bj)) ltac:(rewrite HL; unfold ubn in *; lia))) as HU'.
    assert (Q8' : q64 mem' (spk g 8) (buf + 12)).
    { eapply bytes_at_transport; [exact Q8 | exact MU | apply D; dj]. }
    assert (Q16' : q64 mem' (spk g 16) TSK).
    { eapply bytes_at_transport; [exact Q16 | exact MU | apply D; dj]. }
    assert (EO : uout1 g (upos g (uQ g p)) = UN.psn_out h (uswz g =? 1) (uF g) (ucap g) (upos g (uQ g p))).
    { rewrite psn_out_UP. unfold PN.psn_out. rewrite (proj2 (Z.eqb_neq h 0)) by lia. reflexivity. }
    rewrite EO.
    eapply (ps_next_step B APIf ra empty FF (HNEXT _) g 3 (HB3 g b h buf) [(b, un g); (h, 1304)] L A regs' mem' md
      (spk g 48) buf (ucap g) (spk g 40) h (uswz g) b (upos g (uQ g p)) fl mdv _ _ _ (wz 0) (wz 0) (wz (-1)) pad bj
      (uF g) (uafter g (upos g (uQ g p))) (Post_o B APIf ra g) FR' HP Hfrm).
    + rewrite K1. apply ug_ret_ok; lia.
    + exact K10.
    + exact K11.
    + exact K12.
    + exact K13.
    + unfold spk; lia.
    + unfold spk; lia.
    + unfold spk. Z.div_mod_to_equations. lia.
    + exact HPS'.
    + exact (Permutation_sym (Permutation_cons_append [(b, un g); (h, 1304)] (buf, ubn g))).
    + exact HU'.
    + exact HL.
    + lia.
    + intros _. unfold spk. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|].
      exact (rw_rel _ _ _ _ HR D40).
    + intros _. split; [cbn [In]; right; left; reflexivity|]. split; [cbn [In]; left; reflexivity|].
      split; [exact HMS'|]. split; [exact (uswz_01 g)|]. unfold un, zlen in HN; lia.
    + exact HEF'.
    + intros regs2 mem2 Ft fc2 mdv2 Hfc HFt HF2 RP2 KF KH KI KSTD HEF2 HGU2 H0 H1.
      rewrite (ss_segs B APIf ra empty FF) in KF, KH, KI.
      destruct (H1 ltac:(lia)) as (R10 & MS2 & PS2 & (bj2 & HU2 & HL2 & HF2') & TS2).
      rewrite ?psn_q_UP, ?res_of_UP in R10.
      rewrite ?psn_q_UP, ?pos_of_UP in MS2.
      rewrite ?ps_cells_UP, ?lol_of_UP, ?psn_lh_UP, ?vt_of_UP, ?psn_q_UP, ?vid_of_UP in PS2.
      specialize (TS2 ltac:(unfold spk; lia)). rewrite ?ts_of_UP, ?psn_q_UP in TS2.
      rewrite ?is_fit_kind_UP, ?psn_q_UP, ?incl_UP, ?rec_bytes_UP in HF2'.
      assert (CS : forall k, callee_saved k -> getr regs2 (Z_to_bv 5 k) = getr regs' (Z_to_bv 5 k)) by exact RP2.
      rewrite K1. apply H6. exists b, h, buf. split; [exact Hgood|].
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc2) g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z) 3 (HB3 g b h buf) _ L A regs2 mem2 md Hfc HF2 HP).
      split.
      { (* WKEEP *)
        split; [transitivity (getr regs' 8); [exact (CS 8 ltac:(unfold callee_saved; lia)) | exact H8']|].
        split; [transitivity (getr regs' 9); [exact (CS 9 ltac:(unfold callee_saved; lia)) | exact H9']|].
        split; [transitivity (getr regs' 26); [exact (CS 26 ltac:(unfold callee_saved; lia)) | exact H26']|].
        split.
        { split; [exact (KSTD Hstd')|]. split; [exact HGU2|]. split; [exists fl, mdv2; exact HEF2|]. split.
          - apply (tr_mb_bytes mem' mem2 _ _); [|exact Q0']. intros j Hj. rewrite length_le8 in Hj.
            apply KF; unfold spk, fsp, SLOT_FRAME in *; lia.
          - apply (tr_mb_bytes mem' mem2 _ _); [|exact QL']. intros j Hj. rewrite length_le8 in Hj.
            apply KI; [apply img_w_iff; right; left; unfold G_FILE_LEN in *; lia
                      | unfold G_FILE_LEN, A_STDERR in *; lia]. }
        split.
        { apply (tr_mb_bytes mem' mem2 _ _); [|exact QG']. intros j Hj. rewrite length_le8 in Hj.
          apply KI; [apply img_w_iff; right; left; unfold G_FILE_LEN in *; lia | unfold G_FILE_LEN, A_STDERR in *; lia]. }
        split; [exact (proj1 (mstl_bytes _ _ _ _ _ _ _ MS2))|].
        apply (tr_mb_bytes mem' mem2 _ _); [|exact Q24']. intros j Hj. rewrite length_le8 in Hj.
        apply KF; unfold spk, fsp, SLOT_FRAME in *; lia. }
      split.
      { (* RECST at the new position *)
        split; [exact MS2|].
        split.
        { apply (tr_img_rw mem' mem2 A_OFL_HEAD _); [|exact HOO']. intros j Hj. cbn [cells_size csize] in Hj.
          assert (Wj : img_w (A_OFL_HEAD + j)) by (right; left; lia).
          split; [exact Wj | apply KI; [exact Wj | unfold A_OFL_HEAD, A_STDERR; lia]]. }
        split; [do 3 eexists; exists pad; exact PS2|].
        split; [exact TS2|].
        exists bj2. split; [exact HU2|]. split; [rewrite HL2; exact HL | exact HF2']. }
      split; [lia|]. split; [exact Hpi|]. split; [exact Hp1n|].
      split; [exact R10|].
      split; [transitivity (getr regs' 18); [exact (CS 18 ltac:(unfold callee_saved; lia)) | exact K18]|].
      split; [transitivity (getr regs' 20); [exact (CS 20 ltac:(unfold callee_saved; lia)) | exact K20]|].
      split; [transitivity (getr regs' 25); [exact (CS 25 ltac:(unfold callee_saved; lia)) | exact K25]|].
      split; [transitivity (getr regs' 27); [exact (CS 27 ltac:(unfold callee_saved; lia)) | exact K27]|].
      split.
      { apply (tr_mb_bytes mem' mem2 _ _); [|exact Q8']. intros j Hj. rewrite length_le8 in Hj.
        apply KF; unfold spk, fsp, SLOT_FRAME in *; lia. }
      split.
      { apply (tr_mb_bytes mem' mem2 _ _); [|exact Q16']. intros j Hj. rewrite length_le8 in Hj.
        apply KF; unfold spk, fsp, SLOT_FRAME in *; lia. }
      apply (tr_frw g 3 _ L A regs2 mem2 md mem' (spk g 32) _ HF2);
        [unfold spk; lia | unfold spk; cbn [cells_size csize]; lia | | exact (rw_rel _ _ _ _ HR D32)].
      intros j Hj. cbn [cells_size csize] in Hj. apply KF; unfold spk, fsp, SLOT_FRAME in *; lia.
Qed.

(* The walk's loop (URec.uk4_all): every K4 state outputs the rest of the walk and the call after the reopen. *)
Lemma ug_walk : Hcut_o B APIf ra (Inv_K130a4 B APIf ra empty) uC0 -> forall g i p, HC4 B APIf ra empty g i p.
Proof. intros HT. exact (uk4_all B APIf ra empty ug_L ug_L2 (ug_W HT)). Qed.

(* 0x12e04, the first call of the walk answered: the rest of the run outputs uafter g 24. *)
Lemma ug_K12e3c : Hcut_o B APIf ra (Inv_K130a4 B APIf ra empty) uC0 ->
  Hcut_o B APIf ra (Inv_K12e3c B APIf ra empty) (fun g => uafter g 24).
Proof. intros HT g c Hc. exact (ug_D g (ug_W HT g) (ug_walk HT g) c Hc). Qed.

(* Cut-free twins (SROcf; the cut statements in the PInvCF.Hcut_cf form, URec.HC4_cf/HC5_cf/HC6_cf) of the walk's
   glue: the same proofs through the cut-free steps. Each cut takes the slot's cap bound sb_cap (g_b g) <= CAP_AG and
   passes it on to the next. *)
Hypothesis HCLOSECF : forall fx0 : YK11.FPState, pcap_source_close_contract_cf (fx := fx0) B (APIf rc).
Hypothesis HNEXTCF : forall fx0 : YK11.FPState, @pcap_source_next_contract_cf fx0.

Lemma ug_L2_cf : forall g i p, HC4_cf B APIf ra empty g i p -> HC5_cf B APIf ra empty g p -> HC6_cf B APIf ra empty g i p.
Proof.
  intros g i p H4 H5 c Hcap (b & h & buf & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPr).
  destruct HPr as (HWK & HREC & Hi & Hp & Hpn & E10 & E18 & E20 & E25 & E27 & Q8 & Q16 & C32).
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (ss_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof (ures_range g (uQ g p)) as Hn.
  set (n' := ures g (uQ g p)) in *.
  set (Q := fun (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) =>
    m' = normalize rsegs mem /\
    ((0 < n' /\ pc' = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1ec)%Z)) \/ (n' <= 0 /\ pc' = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x400)%Z))) /\
    getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
    getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 13 = wz (ufirst g) /\
    getr R 18 = getr regs 18 /\ getr R 20 = getr regs 20 /\ getr R 21 = wz n' /\
    getr R 25 = getr regs 25 /\ getr R 26 = getr regs 26 /\ getr R 27 = wz (ufirst g)).
  apply (ss_kA_run_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z)) mem md Q (uafter g p) (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (ss_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of.
    eapply evt_mono; [exact (ubs_L2_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) n' (ufirst g) E10 Hn E27)|].
    intros ms [(P & ->) | (P & ->)]; (do 3 eexists; split; [reflexivity|]);
      (split; [reflexivity|]); (split; [first [left; split; [exact P | reflexivity] | right; split; [exact P | reflexivity]]|]);
      repeat split; reflexivity.
  - intros R pc' m' regs' mem' (-> & HB & G2 & G3 & G4 & G8 & G9 & G13 & G18 & G20 & G21 & G25 & G26 & G27)
      XR HR HS.
    destruct (ug_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 3 (HB3 g b h buf) L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
        | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM | intros lo hi y [] ]. }
    assert (K8 : getr regs' 8 = getr regs 8) by (rewrite (ss_getr_eqv _ _ 8 XR); exact G8).
    assert (K9 : getr regs' 9 = getr regs 9) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
    assert (K26 : getr regs' 26 = getr regs 26) by (rewrite (ss_getr_eqv _ _ 26 XR); exact G26).
    pose proof (tr0_WKEEP g b buf regs regs' mem mem' MU WM K8 K9 K26 HWK) as WK'.
    pose proof (tr0_RECST g b h buf p mem mem' MU WM HREC) as RC'.
    destruct HB as [(P & ->) | (P & ->)].
    + assert (K : ukind g (uQ g p) = PN.KFit) by (apply ures_pos; exact P).
      rewrite (uafter_fit g p K). apply (H4 _ Hcap).
      exists b, h, buf, (wz (ufirst g)). split; [exact Hgood|].
      exists fx', L, A, regs', mem', md. split; [reflexivity|]. split; [exact Hfrm|]. split; [exact FR'|].
      split; [exact HP|].
      split; [exact WK'|]. split; [exact RC'|].
      split; [lia|]. split; [lia|]. split; [exact K|].
      split; [rewrite (ss_getr_eqv _ _ 18 XR); rewrite G18; exact E18|].
      split; [rewrite (ss_getr_eqv _ _ 20 XR); rewrite G20; exact E20|].
      split; [rewrite (ss_getr_eqv _ _ 21 XR); exact G21|].
      split; [rewrite (ss_getr_eqv _ _ 25 XR); rewrite G25; exact E25|].
      split; [rewrite (ss_getr_eqv _ _ 27 XR); exact G27|].
      split; [rewrite (ss_getr_eqv _ _ 13 XR); exact G13|].
      split; [right; split; [lia | reflexivity]|].
      split; [exact (tr0_bytes _ _ _ _ MU Q8)|]. split; [exact (tr0_bytes _ _ _ _ MU Q16)|].
      exact (tr0_rw _ _ _ _ MU WM C32).
    + assert (K : ukind g (uQ g p) <> PN.KFit) by (intros K; apply ures_pos in K; lia).
      rewrite (uafter_nfit g p K). apply (H5 _ Hcap).
      exists b, h, buf. split; [exact Hgood|].
      exists fx', L, A, regs', mem', md. split; [reflexivity|]. split; [exact Hfrm|]. split; [exact FR'|].
      split; [exact HP|].
      split; [exact WK'|]. split; [exact RC'|].
      split; [lia|]. split; [exact Hpn|]. split; [exact K|].
      split; [rewrite (ss_getr_eqv _ _ 21 XR); exact G21|].
      split; [rewrite (ss_getr_eqv _ _ 25 XR); rewrite G25; exact E25|].
      rewrite (ss_getr_eqv _ _ 27 XR); exact G27.
Qed.

Lemma ug_W_cf : Hcut_cf B APIf ra (Inv_K130a4 B APIf ra empty) uC0 -> forall g p, HC5_cf B APIf ra empty g p.
Proof.
  intros HT g p c Hcap (b & h & buf & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPr).
  destruct HPr as (HWK & HREC & Hp & Hpn & K & E21 & E25 & E27).
  pose proof HWK as (H8 & H9 & H26 & (Hstd & Hgd & Herr & Q0 & QL) & QG & HBF & Q24).
  pose proof HREC as (HMS & HOO & (lol & lvt & lvid & pad & HPS) & HTS & (bj & HU & HL & HFT)).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (ss_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & _).
  pose proof (un_range g HGV) as HN.
  pose proof (@YM05.alloc_ceiling_lt rc) as HAC.
  destruct (ss_hb_blk B APIf ra empty FF g 3 _ L A regs mem md b (un g) HF HP
    ltac:(unfold HB3; cbn [In]; left; reflexivity)) as (_ & Hb1 & Hb2 & _).
  assert (USP : bv_unsigned (getr regs 2) = fsp g)
    by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
  assert (HE : 0 <= p <= PN.flen (uF g)) by (unfold PN.flen; unfold un, zlen in Hpn; lia).
  assert (HFn : bytes_at rsegs (normalize rsegs mem) b (uF g)) by (apply bytes_at_normalize; [exact HMI | exact HBF]).
  assert (Q0n : bytes_at rsegs (normalize rsegs mem) (fsp g) (le8 (wz (ud g)))).
  { apply bytes_at_normalize; [exact HMI|]. unfold q64, spk in Q0. rewrite Z.add_0_r in Q0. exact Q0. }
  assert (QLn : bytes_at rsegs (normalize rsegs mem) (symaddr Symbols.Ubsan.s_g_file_len) (le8 (wz (PN.flen (uF g)))))
    by (apply bytes_at_normalize; [exact HMI | exact QL]).
  assert (Q56n : bytes_at rsegs (normalize rsegs mem) (fsp g + 56) (le4 (wz (uswz g)))).
  { apply bytes_at_normalize; [exact HMI|]. destruct (psc_parts _ _ _ _ _ _ _ _ HPS) as (S1 & _).
    unfold spk in S1. replace (fsp g + 56) with (fsp g + 48 + 8) by lia. exact S1. }
  pose proof (proj1 (PW.kind_nfit (usw g) (uF g) (ucap g) (uQ g p) K)) as EA.
  set (Q := fun (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) =>
    m' = normalize rsegs mem /\ pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_close) /\ getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z) /\
    getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
    getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 10 = wz (fsp g + 48) /\
    getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27).
  apply (ss_kA_run_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x400)%Z)) mem md Q (uC0 g) (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (ss_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of.
    eapply evt_mono; [exact (ubs_W_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (uF g) (usw g) (fsp g) (ures g (uQ g p)) p (uQ g p) (ucap g) (ud g) b (uswz g)
      rd32f_holds USP E21 EA K E25 HE (PW.psn_q_skips (usw g) (uF g) (ucap g) p ltac:(lia)) H8 ltac:(lia)
      ltac:(unfold PN.flen; unfold un, zlen in Hb2; lia) HFn H9 eq_refl (ud_range g) Q0n H26 QLn Q56n
      (uswz_01 g) eq_refl ltac:(unfold PN.flen; unfold un, zlen in HN; lia))|].
    intros ms (a1' & a2' & a3' & a4' & a5' & s2' & s3' & s4' & s9' & ->).
    do 3 eexists. split; [reflexivity|]. repeat split; reflexivity.
  - intros R pc' m' regs' mem' (-> & -> & G1 & G2 & G3 & G4 & G8 & G9 & G10 & G26 & G27) XR HR HS.
    destruct (ug_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 3 (HB3 g b h buf) L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
        | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM | intros lo hi y [] ]. }
    assert (K1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
    assert (K8 : getr regs' 8 = getr regs 8) by (rewrite (ss_getr_eqv _ _ 8 XR); exact G8).
    assert (K9 : getr regs' 9 = getr regs 9) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
    assert (K10 : getr regs' 10 = wz (spk g 48)) by (rewrite (ss_getr_eqv _ _ 10 XR); exact G10).
    assert (K26 : getr regs' 26 = getr regs 26) by (rewrite (ss_getr_eqv _ _ 26 XR); exact G26).
    assert (K27 : getr regs' 27 = getr regs 27) by (rewrite (ss_getr_eqv _ _ 27 XR); exact G27).
    pose proof (tr0_WKEEP g b buf regs regs' mem mem' MU WM K8 K9 K26 HWK) as WK'.
    pose proof WK' as (H8' & H9' & H26' & (Hstd' & Hgd' & Herr' & Q0' & QL') & QG' & HBF' & Q24').
    pose proof (tr0_rw _ _ _ _ MU WM HPS) as HPS'.
    pose proof (mstl_transport [] mem mem' h b (uF g) _ _ _ HMS MU WM I I) as HMS'.
    pose proof (tr0_rw _ _ _ _ MU WM HOO) as HOO'.
    pose proof (Arr.u8arr_transport rsegs [] mem mem' buf bj HU MU WM I) as HU'.
    eapply (ps_close_step_cf B APIf ra empty FF (HCLOSECF _) g 3 [(b, un g)] h [(buf, ubn g)] L A regs' mem' md
      (spk g 48) (wz (uswz g)) _ _ _ pad b (uF g) (upos g (uQ g p)) (uC0 g) (Post_o B APIf ra g) FR' HP).
    + rewrite K1. apply ug_ret_ok; lia.
    + exact K10.
    + unfold spk; lia.
    + unfold spk, fsp, SLOT_FRAME; lia.
    + unfold spk. Z.div_mod_to_equations. lia.
    + exact HPS'.
    + cbn [app In]. left. reflexivity.
    + exact HMS'.
    + exact HOO'.
    + exact Hstd'.
    + intros L2 A2 regs2 mem2 md2 HF2 HP2 RP2 KF KB KI HPS2 HOE2 HSTD2 HGU2 HBF2.
      rewrite (ss_segs B APIf ra empty FF) in KF, KB, KI.
      rewrite K1. apply (HT g _ Hcap). exists b, buf. split; [exact Hgood|].
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z) 3 [(b, un g); (buf, ubn g)] _ L2 A2 regs2 mem2 md2 Hfrm HF2
        HP2).
      split; [split; [|split]|split].
      * split; [transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia)) | exact H8']|].
        split; [transitivity (getr regs' 9); [exact (RP2 9 ltac:(unfold callee_saved; lia)) | exact H9']|].
        split; [transitivity (getr regs' 26); [exact (RP2 26 ltac:(unfold callee_saved; lia)) | exact H26']|].
        split.
        { split; [exact HSTD2|]. split; [exact HGU2|]. split.
          - apply (tr_errf_se mem' mem2); [|exact Herr']. intros x Hx.
            apply KI; [right; right; exact Hx | unfold A_STDERR, A_OFL_HEAD in *; lia].
          - split.
            + apply (tr_mb_bytes mem' mem2 _ _); [|exact Q0']. intros i Hi. rewrite length_le8 in Hi.
              apply KF; unfold spk, fsp, SLOT_FRAME in *; lia.
            + apply (tr_mb_bytes mem' mem2 _ _); [|exact QL']. intros i Hi. rewrite length_le8 in Hi.
              apply KI; [apply img_w_iff; right; left; unfold G_FILE_LEN in *; lia
                        | unfold G_FILE_LEN, A_OFL_HEAD in *; lia]. }
        split.
        { apply (tr_mb_bytes mem' mem2 _ _); [|exact QG']. intros i Hi. rewrite length_le8 in Hi.
          apply KI; [apply img_w_iff; right; left; unfold G_FILE_LEN in *; lia | unfold G_FILE_LEN, A_OFL_HEAD in *; lia]. }
        split; [exact HBF2|].
        apply (tr_mb_bytes mem' mem2 _ _); [|exact Q24']. intros i Hi. rewrite length_le8 in Hi.
        apply KF; unfold spk, fsp, SLOT_FRAME in *; lia.
      * transitivity (getr regs' 27); [exact (RP2 27 ltac:(unfold callee_saved; lia))|]. rewrite K27. exact E27.
      * exists bj. split; [|exact HL].
        destruct (ss_hb_blk B APIf ra empty FF g 3 _ L2 A2 regs2 mem2 md2 buf (ubn g) HF2 HP2
          ltac:(cbn [app In]; right; left; reflexivity)) as (W & _).
        rewrite (ss_segs B APIf ra empty FF) in W.
        apply (tr_u8 mem' mem2 buf bj); [|exact HU']. intros i Hi. rewrite HL in Hi.
        split; [exact (proj1 (W i Hi)) | apply (KB buf (ubn g) i); [cbn [app In]; right; left; reflexivity | exact Hi]].
      * exact HOE2.
      * do 3 eexists. exists pad. exact HPS2.
Qed.

Lemma ug_D_cf : forall g, (forall p, HC5_cf B APIf ra empty g p) -> (forall i p, HC4_cf B APIf ra empty g i p) ->
  forall c, sb_cap (g_b g) <= CAP_AG -> Inv_K12e3c B APIf ra empty g c ->
    SROcf (ms_segs B) c (uafter g 24) (Post_o B APIf ra g).
Proof.
  intros g H5 H4 c Hcap (b & h & buf & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPr).
  destruct HPr as (E10 & E18 & HWK & HREC).
  pose proof HWK as (H8 & _).
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (ss_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (hb3_bnd fx' g b h buf 3 L A regs mem md HF HP)
    as (Hf & Hb0 & Hb & Hh0 & Hhb & Hbuf0 & Hbuf & Hfsp & HS47 & H16 & HK & HAC & _ & _ & _ & USP).
  pose proof (ss_fr_stk B APIf ra empty FF g _ _ L A regs mem md HF) as HST.
  assert (HST' : stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (fsp g + 176)) by (rewrite Hfsp; exact HST).
  destruct (c8_of_stk _ _ _ (fsp g + 8) HST ltac:(lia) ltac:(lia)) as (v8 & R8).
  destruct (c8_of_stk _ _ _ (fsp g + 16) HST ltac:(lia) ltac:(lia)) as (v16 & R16).
  destruct (c8_of_stk _ _ _ (fsp g + 32) HST ltac:(lia) ltac:(lia)) as (v32 & R32).
  set (W := [(fsp g + 8, fsp g + 24); (fsp g + 32, fsp g + 40)]).
  set (Q := fun (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) =>
    ((0 < ufirst g /\ pc' = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1ec)%Z) /\ munch W (normalize rsegs mem) m' /\
      wmono rsegs (normalize rsegs mem) m' /\ rw_cells rsegs m' (fsp g + 8) [C8 (wz (buf + 12))] /\
      rw_cells rsegs m' (fsp g + 16) [C8 (wz (1000000 * 2 ^ 32))] /\ rw_cells rsegs m' (fsp g + 32) [C8 (wz 0)] /\
      getr R 18 = wz (-8) /\ getr R 20 = bv_not (wz b)) \/
     (ufirst g <= 0 /\ pc' = Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x400)%Z) /\ m' = normalize rsegs mem)) /\
    getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = wz b /\
    getr R 9 = getr regs 9 /\ getr R 21 = wz (ufirst g) /\ getr R 25 = wz 24 /\ getr R 26 = getr regs 26 /\
    getr R 27 = wz (ufirst g)).
  apply (ss_kA_run_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1b8)%Z)) mem md Q (uafter g 24) (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (ss_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of.
    eapply evt_mono; [exact (ubs_D_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (g_S g - SLOT_K) (fsp g) (ufirst g) b buf v8 v16 v32 USP E10 (ures_range g (uQ g 24))
      H8 E18 R8 R16 R32 (mem_inv_normalize rsegs mem) HST')|].
    intros ms [(P & m1 & -> & MU0 & WM0 & _ & _ & D8 & D16 & D32) | (P & ->)];
      do 3 eexists; (split; [reflexivity|]).
    + split; [left; split; [exact P|]; split; [reflexivity|]; split; [exact MU0|]; split; [exact WM0|];
        split; [exact D8|]; split; [exact D16|]; split; [exact D32|]; split; reflexivity|].
      repeat split; reflexivity.
    + split; [right; split; [exact P|]; split; reflexivity|]. repeat split; reflexivity.
  - intros R pc' m' regs' mem' ([(P & -> & MU0 & WM0 & D8 & D16 & D32 & G18 & G20) | (P & -> & ->)] &
      G2 & G3 & G4 & G8 & G9 & G21 & G25 & G26 & G27) XR HR HS.
    + pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
      pose proof (munch_rel rsegs W mem _ mem' _ HR0 HR HS MU0) as MU.
      pose proof (wmono_rel rsegs mem _ mem' _ HR0 HR HS WM0) as WM.
      assert (FR' : FR B APIf ra empty g 3 (HB3 g b h buf) L A regs' mem' md).
      { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' W HF HP);
          [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
          | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM |].
        intros lo hi y Hin Hy. left. unfold W in Hin. destruct Hin as [E|[E|[]]]; injection E as <- <-; lia. }
      assert (K8 : getr regs' 8 = getr regs 8) by (rewrite (ss_getr_eqv _ _ 8 XR), G8; symmetry; exact H8).
      assert (K9 : getr regs' 9 = getr regs 9) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
      assert (K26 : getr regs' 26 = getr regs 26) by (rewrite (ss_getr_eqv _ _ 26 XR); exact G26).
      pose proof (trW_WKEEP g b buf regs regs' mem mem' W MU WM
        ltac:(intros lo hi Hin; unfold W in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-; lia)
        Hf Hb K8 K9 K26 HWK) as WK'.
      pose proof (trW_RECST g b h buf 24 mem mem' W MU WM
        ltac:(intros lo hi Hin; unfold W in Hin; destruct Hin as [E|[E|[]]]; injection E as <- <-; lia)
        Hf Hb Hhb Hbuf HREC) as RC'.
      assert (K : ukind g (uQ g 24) = PN.KFit) by (apply ures_pos; exact P).
      rewrite (uafter_fit g 24 K). apply (H4 0 24 _ Hcap).
      exists b, h, buf, (getr regs' 13). split; [exact Hgood|].
      exists fx', L, A, regs', mem', md. split; [reflexivity|]. split; [exact Hfrm|]. split; [exact FR'|].
      split; [exact HP|].
      split; [exact WK'|]. split; [exact RC'|].
      split; [lia|]. split; [lia|]. split; [exact K|].
      split; [rewrite (ss_getr_eqv _ _ 18 XR); exact G18|].
      split; [rewrite (ss_getr_eqv _ _ 20 XR); exact G20|].
      split; [rewrite (ss_getr_eqv _ _ 21 XR); exact G21|].
      split; [rewrite (ss_getr_eqv _ _ 25 XR); exact G25|].
      split; [rewrite (ss_getr_eqv _ _ 27 XR); exact G27|].
      split; [reflexivity|].
      split; [left; split; reflexivity|].
      split; [exact (q64_of_rw _ _ _ (rw_rel _ _ _ _ HR D8))|].
      split; [exact (q64_of_rw _ _ _ (rw_rel _ _ _ _ HR D16))|].
      exact (rw_rel _ _ _ _ HR D32).
    + destruct (ug_same mem mem' HMI HR HS) as (MU & WM).
      assert (FR' : FR B APIf ra empty g 3 (HB3 g b h buf) L A regs' mem' md).
      { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' [] HF HP);
          [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
          | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM | intros lo hi y [] ]. }
      assert (K8 : getr regs' 8 = getr regs 8) by (rewrite (ss_getr_eqv _ _ 8 XR), G8; symmetry; exact H8).
      assert (K9 : getr regs' 9 = getr regs 9) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
      assert (K26 : getr regs' 26 = getr regs 26) by (rewrite (ss_getr_eqv _ _ 26 XR); exact G26).
      pose proof (tr0_WKEEP g b buf regs regs' mem mem' MU WM K8 K9 K26 HWK) as WK'.
      pose proof (tr0_RECST g b h buf 24 mem mem' MU WM HREC) as RC'.
      assert (K : ukind g (uQ g 24) <> PN.KFit) by (intros K; apply ures_pos in K; unfold ufirst in P; lia).
      rewrite (uafter_nfit g 24 K). apply (H5 24 _ Hcap).
      exists b, h, buf. split; [exact Hgood|].
      exists fx', L, A, regs', mem', md. split; [reflexivity|]. split; [exact Hfrm|]. split; [exact FR'|].
      split; [exact HP|].
      split; [exact WK'|]. split; [exact RC'|].
      split; [lia|]. split; [exact (ugood_len g Hgood)|]. split; [exact K|].
      split; [rewrite (ss_getr_eqv _ _ 21 XR); exact G21|].
      split; [rewrite (ss_getr_eqv _ _ 25 XR); exact G25|].
      rewrite (ss_getr_eqv _ _ 27 XR); exact G27.
Qed.

Lemma ug_L_cf : forall g i p, HC6_cf B APIf ra empty g (i + 1) (upos g (uQ g p)) ->
  forall c, sb_cap (g_b g) <= CAP_AG -> Inv_K4 B APIf ra empty g i p c ->
    SROcf (ms_segs B) c (uout1 g (upos g (uQ g p)) ++ uafter g (upos g (uQ g p))) (Post_o B APIf ra g).
Proof.
  intros g i p H6 c Hcap (b & h & buf & a3 & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HPr).
  destruct HPr as (HWK & HREC & Hi & Hp & K & E18 & E20 & E21 & E25 & E27 & E13 & HI & Q8 & Q16 & C32).
  pose proof HWK as (H8 & H9 & H26 & (Hstd & Hgd & Herr & Q0 & QL) & QG & HBF & Q24).
  pose proof HREC as (HMS & HOO & (lol & lvt & lvid & pad & HPS) & HTS & (bj & HU & HL & HFT)).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (ss_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (hb3_bnd fx' g b h buf 3 L A regs mem md HF HP)
    as (Hf & Hb0 & Hb & Hh0 & Hhb & Hbuf0 & Hbuf & Hfsp & HS47 & H16 & HK & HAC & Hbc & Hhc & Hbufc & USP).
  pose proof (un_range g HGV) as HN. pose proof (ugood_len g Hgood) as H24.
  pose proof (ucap_range g) as HC.
  pose proof (@YM05.alloc_ceiling_lt rc) as HACL.
  pose proof (ss_fr_stk B APIf ra empty FF g _ _ L A regs mem md HF) as HST.
  assert (HST' : stk rsegs (normalize rsegs mem) (g_S g - SLOT_K) (fsp g + 176)) by (rewrite Hfsp; exact HST).
  destruct (PW.kind_fit (usw g) (uF g) (ucap g) (uQ g p) K) as (KR & KL & KP & KE & KIc).
  assert (EP : upos g (uQ g p) = uQ g p + 16 + PN.incl (usw g) (uF g) (uQ g p)) by exact KP.
  destruct (upos_fit g p ltac:(lia) K) as (Hp1 & Hp1n).
  pose proof (PW.walk_pos_step (usw g) (uF g) (ucap g) p i Hp K) as Hpi.
  (* The facts of the segment, on the normalized memory. *)
  assert (E21' : getr regs 21 = wz (PN.rec_len (usw g) (uF g) (uQ g p))) by (rewrite E21; unfold ures; rewrite KR; reflexivity).
  assert (HI' : (i = 0 /\ ufirst g = PN.rec_len (usw g) (uF g) (uQ g p)) \/ (0 < i /\ getr regs 13 = wz (ufirst g))).
  { destruct HI as [(-> & ->) | (Hi0 & Ea)];
      [left; split; [reflexivity | unfold ufirst, ures; exact KR] | right; split; [exact Hi0 | rewrite E13; exact Ea]]. }
  assert (HFn : bytes_at rsegs (normalize rsegs mem) b (uF g)) by (apply bytes_at_normalize; [exact HMI | exact HBF]).
  pose proof (bytes_at_normalize rsegs mem _ _ HMI QL) as QLn.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI Q8) as Q8n.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI Q16) as Q16n.
  pose proof (bytes_at_normalize rsegs mem _ _ HMI Q24) as Q24n.
  assert (C32n : rw_cells rsegs (normalize rsegs mem) (spk g 32) [C8 (wz i)])
    by (apply rw_norm; [exact HMI | unfold IMG_HI, spk; lia | unfold spk; cbn [cells_size csize]; lia | exact C32]).
  rewrite (PW.ts_of_fit (usw g) (uF g) (ucap g) (uQ g p) (wz (-1)) K) in HTS.
  assert (TSn : rw_cells rsegs (normalize rsegs mem) (spk g 40) [C8 (wz (PN.rec_ts (usw g) (uF g) (uQ g p)))])
    by (apply rw_norm; [exact HMI | unfold IMG_HI, spk; lia | unfold spk; cbn [cells_size csize]; lia | exact HTS]).
  destruct (psc_parts _ _ _ _ _ _ _ _ HPS) as (S1 & S2 & S3 & S4). unfold spk in S1, S2, S3, S4.
  rewrite (PW.lol_of_fit (usw g) (uF g) (ucap g) p lol ltac:(lia) K) in S2.
  rewrite (PW.vt_of_fit (usw g) (uF g) (ucap g) (uQ g p) lvt K) in S3.
  rewrite (PW.vid_of_fit (usw g) (uF g) (ucap g) (uQ g p) lvid K) in S4.
  assert (S1n : bytes_at rsegs (normalize rsegs mem) (fsp g + 56) (le4 (wz (uswz g)))).
  { apply bytes_at_normalize; [exact HMI|]. replace (fsp g + 56) with (fsp g + 48 + 8) by lia. exact S1. }
  assert (S2n : bytes_at rsegs (normalize rsegs mem) (fsp g + 60) (le4 (wz (PN.orig (usw g) (uF g) (uQ g p))))).
  { apply bytes_at_normalize; [exact HMI|]. replace (fsp g + 60) with (fsp g + 48 + 12) by lia. exact S2. }
  assert (S3n : bytes_at rsegs (normalize rsegs mem) (fsp g + 64)
    (le4 (wz (if PN.tagged (usw g) (uF g) (uQ g p) then 1 else 0)))).
  { apply bytes_at_normalize; [exact HMI|]. replace (fsp g + 64) with (fsp g + 48 + 16) by lia.
    revert S3. destruct (PN.tagged (usw g) (uF g) (uQ g p)); intros S3; exact S3. }
  assert (S4n : bytes_at rsegs (normalize rsegs mem) (fsp g + 68)
    (le2 (wz (if PN.tagged (usw g) (uF g) (uQ g p) then PN.rec_vid (uF g) (uQ g p) else 0)))).
  { apply bytes_at_normalize; [exact HMI|]. replace (fsp g + 68) with (fsp g + 48 + 20) by lia.
    revert S4. destruct (PN.tagged (usw g) (uF g) (uQ g p)); intros S4; exact S4. }
  assert (HBUFn : bytes_at rsegs (normalize rsegs mem) buf (PN.rec_bytes (usw g) (uF g) (uQ g p))).
  { apply bytes_at_normalize; [exact HMI|]. exact (u8_prefix mem buf bj _ _ HU (HFT ltac:(rewrite K; reflexivity))). }
  set (Qn := uQ g p + 16 + PN.incl (usw g) (uF g) (uQ g p)).
  set (Q := fun (R : bvmap 5 word) (pc' : word) (m' : word -> option byte) =>
    pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next) /\ munch [(fsp g + 32, fsp g + 48)] (normalize rsegs mem) m' /\
    wmono rsegs (normalize rsegs mem) m' /\ rw_cells rsegs m' (fsp g + 32) [C8 (wz (i + 1))] /\
    rw_cells rsegs m' (fsp g + 40) [C8 (wz (-1))] /\
    getr R 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z) /\ getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
    getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 10 = wz (fsp g + 48) /\ getr R 11 = wz buf /\
    getr R 12 = wz (ucap g) /\ getr R 13 = wz (fsp g + 40) /\ getr R 18 = getr regs 18 /\
    getr R 20 = getr regs 20 /\ getr R 25 = wz Qn /\ getr R 26 = getr regs 26 /\ getr R 27 = getr regs 27).
  apply (ss_kA_run_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x1ec)%Z)) mem md Q _ (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (ss_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of.
    eapply evt_mono; [exact (ubs_L_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (uF g) (usw g) (g_S g - SLOT_K) (fsp g) b buf (ucap g) (uswz g) i p (uQ g p) (ufirst g)
      rd32f_holds BC USP E25 H8 H9 E18 E20 E21' H26 E27 HI' Hi Hp
      (PW.psn_q_skips (usw g) (uF g) (ucap g) p ltac:(lia)) K ltac:(unfold un, zlen in HN; lia) ltac:(lia)
      ltac:(unfold un, zlen in Hb; lia) QLn HFn HC Q8n Q16n Q24n C32n TSn S1n (uswz_01 g) eq_refl S2n S3n S4n
      HBUFn Hbuf0 ltac:(unfold ubn in Hbufc; lia) ltac:(left; unfold un, zlen in Hb; lia)
      ltac:(left; unfold ubn in Hbufc; lia) ltac:(lia) (mem_inv_normalize rsegs mem) HST')|].
    intros ms (t0' & t1' & t2' & a4' & a5' & a6' & a7' & s3' & s5' & s6' & s7' & s8' & t3' & t4' & t5' & t6' & m1 & ->
      & MU0 & WM0 & _ & _ & D32 & D40).
    do 3 eexists. split; [reflexivity|].
    split; [reflexivity|]. split; [exact MU0|]. split; [exact WM0|]. split; [exact D32|]. split; [exact D40|].
    repeat split; reflexivity.
  - intros R pc' m' regs' mem' (-> & MU0 & WM0 & D32 & D40 & G1 & G2 & G3 & G4 & G8 & G9 & G10 & G11 & G12 & G13 &
      G18 & G20 & G25 & G26 & G27) XR HR HS.
    pose proof (mem_rel_normalize rsegs mem HMI) as HR0.
    set (W := [(fsp g + 32, fsp g + 48)]) in MU0.
    pose proof (munch_rel rsegs W mem _ mem' _ HR0 HR HS MU0) as MU.
    pose proof (wmono_rel rsegs mem _ mem' _ HR0 HR HS WM0) as WM.
    assert (FR' : FR B APIf ra empty g 3 (HB3 g b h buf) L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' W HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); exact G2 | rewrite (ss_getr_eqv _ _ 3 XR); exact G3
        | rewrite (ss_getr_eqv _ _ 4 XR); exact G4 | exact MU | exact WM |].
      intros lo hi y Hin Hy. left. unfold W in Hin. destruct Hin as [E|[]]; injection E as <- <-; lia. }
    assert (K1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); exact G1).
    assert (K8 : getr regs' 8 = getr regs 8) by (rewrite (ss_getr_eqv _ _ 8 XR); exact G8).
    assert (K9 : getr regs' 9 = getr regs 9) by (rewrite (ss_getr_eqv _ _ 9 XR); exact G9).
    assert (K10 : getr regs' 10 = wz (spk g 48)) by (rewrite (ss_getr_eqv _ _ 10 XR); exact G10).
    assert (K11 : getr regs' 11 = wz buf) by (rewrite (ss_getr_eqv _ _ 11 XR); exact G11).
    assert (K12 : getr regs' 12 = wz (ucap g)) by (rewrite (ss_getr_eqv _ _ 12 XR); exact G12).
    assert (K13 : getr regs' 13 = wz (spk g 40)) by (rewrite (ss_getr_eqv _ _ 13 XR); exact G13).
    assert (K18 : getr regs' 18 = wz (-8)) by (rewrite (ss_getr_eqv _ _ 18 XR), G18; exact E18).
    assert (K20 : getr regs' 20 = bv_not (wz b)) by (rewrite (ss_getr_eqv _ _ 20 XR), G20; exact E20).
    assert (K25 : getr regs' 25 = wz (upos g (uQ g p))) by (rewrite (ss_getr_eqv _ _ 25 XR), G25, EP; reflexivity).
    assert (K26 : getr regs' 26 = getr regs 26) by (rewrite (ss_getr_eqv _ _ 26 XR); exact G26).
    assert (K27 : getr regs' 27 = wz (ufirst g)) by (rewrite (ss_getr_eqv _ _ 27 XR), G27; exact E27).
    pose proof (trW_WKEEP g b buf regs regs' mem mem' W MU WM
      ltac:(intros lo hi Hin; unfold W in Hin; destruct Hin as [E|[]]; injection E as <- <-; lia)
      Hf Hb K8 K9 K26 HWK) as WK'.
    pose proof WK' as (H8' & H9' & H26' & (Hstd' & Hgd' & (fl & mdv & HEF') & Q0' & QL') & QG' & HBF' & Q24').
    assert (D : forall a n, (a + n <= fsp g + 32 \/ fsp g + 48 <= a) -> disjoint_from W a n).
    { intros a n Ha. unfold W. cbn [disjoint_from]. split; [lia | exact I]. }
    pose proof (mstl_transport W mem mem' h b (uF g) _ _ _ HMS MU WM (D h 1304 ltac:(lia))
      (D b (Z.of_nat (length (uF g))) ltac:(unfold un, zlen in Hb; lia))) as HMS'.
    assert (HOO' : ofl_one mem' h).
    { eapply rw_cells_transport; [exact HOO | exact MU | exact WM | apply D; dj]. }
    assert (HPS' : rw_cells rsegs mem' (spk g 48) (PS.ps_cells (wz h) (wz (uswz g))
      (PN.lol_of (usw g) (uF g) (PN.psn_lh (usw g) (uF g) (ucap g) p) lol)
      (PN.vt_of (usw g) (uF g) (ucap g) (uQ g p) lvt) (PN.vid_of (usw g) (uF g) (ucap g) (uQ g p) lvid) pad)).
    { eapply rw_cells_transport; [exact HPS | exact MU | exact WM | apply D; dj]. }
    pose proof (Arr.u8arr_transport rsegs W mem mem' buf bj HU MU WM
      (D buf (Z.of_nat (length bj)) ltac:(rewrite HL; unfold ubn in *; lia))) as HU'.
    assert (Q8' : q64 mem' (spk g 8) (buf + 12)).
    { eapply bytes_at_transport; [exact Q8 | exact MU | apply D; dj]. }
    assert (Q16' : q64 mem' (spk g 16) TSK).
    { eapply bytes_at_transport; [exact Q16 | exact MU | apply D; dj]. }
    assert (EO : uout1 g (upos g (uQ g p)) = UN.psn_out h (uswz g =? 1) (uF g) (ucap g) (upos g (uQ g p))).
    { rewrite psn_out_UP. unfold PN.psn_out. rewrite (proj2 (Z.eqb_neq h 0)) by lia. reflexivity. }
    rewrite EO.
    eapply (ps_next_step_cf B APIf ra empty FF (HNEXTCF _) g 3 (HB3 g b h buf) [(b, un g); (h, 1304)] L A regs' mem' md
      (spk g 48) buf (ucap g) (spk g 40) h (uswz g) b (upos g (uQ g p)) fl mdv _ _ _ (wz 0) (wz 0) (wz (-1)) pad bj
      (uF g) (uafter g (upos g (uQ g p))) (Post_o B APIf ra g) FR' HP Hfrm).
    + rewrite K1. apply ug_ret_ok; lia.
    + exact K10.
    + exact K11.
    + exact K12.
    + exact K13.
    + unfold spk; lia.
    + unfold spk; lia.
    + unfold spk. Z.div_mod_to_equations. lia.
    + exact HPS'.
    + exact (Permutation_sym (Permutation_cons_append [(b, un g); (h, 1304)] (buf, ubn g))).
    + exact HU'.
    + exact HL.
    + lia.
    + intros _. unfold spk. split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|]. split; [lia|].
      exact (rw_rel _ _ _ _ HR D40).
    + intros _. split; [cbn [In]; right; left; reflexivity|]. split; [cbn [In]; left; reflexivity|].
      split; [exact HMS'|]. split; [exact (uswz_01 g)|]. unfold un, zlen in HN; lia.
    + exact HEF'.
    + intros regs2 mem2 Ft fc2 mdv2 Hfc HFt HF2 RP2 KF KH KI KSTD HEF2 HGU2 H0 H1.
      rewrite (ss_segs B APIf ra empty FF) in KF, KH, KI.
      destruct (H1 ltac:(lia)) as (R10 & MS2 & PS2 & (bj2 & HU2 & HL2 & HF2') & TS2).
      rewrite ?psn_q_UP, ?res_of_UP in R10.
      rewrite ?psn_q_UP, ?pos_of_UP in MS2.
      rewrite ?ps_cells_UP, ?lol_of_UP, ?psn_lh_UP, ?vt_of_UP, ?psn_q_UP, ?vid_of_UP in PS2.
      specialize (TS2 ltac:(unfold spk; lia)). rewrite ?ts_of_UP, ?psn_q_UP in TS2.
      rewrite ?is_fit_kind_UP, ?psn_q_UP, ?incl_UP, ?rec_bytes_UP in HF2'.
      assert (CS : forall k, callee_saved k -> getr regs2 (Z_to_bv 5 k) = getr regs' (Z_to_bv 5 k)) by exact RP2.
      rewrite K1. apply (H6 _ Hcap). exists b, h, buf. split; [exact Hgood|].
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc2) g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x3e8)%Z) 3 (HB3 g b h buf) _ L A regs2 mem2 md Hfc HF2 HP).
      split.
      { (* WKEEP *)
        split; [transitivity (getr regs' 8); [exact (CS 8 ltac:(unfold callee_saved; lia)) | exact H8']|].
        split; [transitivity (getr regs' 9); [exact (CS 9 ltac:(unfold callee_saved; lia)) | exact H9']|].
        split; [transitivity (getr regs' 26); [exact (CS 26 ltac:(unfold callee_saved; lia)) | exact H26']|].
        split.
        { split; [exact (KSTD Hstd')|]. split; [exact HGU2|]. split; [exists fl, mdv2; exact HEF2|]. split.
          - apply (tr_mb_bytes mem' mem2 _ _); [|exact Q0']. intros j Hj. rewrite length_le8 in Hj.
            apply KF; unfold spk, fsp, SLOT_FRAME in *; lia.
          - apply (tr_mb_bytes mem' mem2 _ _); [|exact QL']. intros j Hj. rewrite length_le8 in Hj.
            apply KI; [apply img_w_iff; right; left; unfold G_FILE_LEN in *; lia
                      | unfold G_FILE_LEN, A_STDERR in *; lia]. }
        split.
        { apply (tr_mb_bytes mem' mem2 _ _); [|exact QG']. intros j Hj. rewrite length_le8 in Hj.
          apply KI; [apply img_w_iff; right; left; unfold G_FILE_LEN in *; lia | unfold G_FILE_LEN, A_STDERR in *; lia]. }
        split; [exact (proj1 (mstl_bytes _ _ _ _ _ _ _ MS2))|].
        apply (tr_mb_bytes mem' mem2 _ _); [|exact Q24']. intros j Hj. rewrite length_le8 in Hj.
        apply KF; unfold spk, fsp, SLOT_FRAME in *; lia. }
      split.
      { (* RECST at the new position *)
        split; [exact MS2|].
        split.
        { apply (tr_img_rw mem' mem2 A_OFL_HEAD _); [|exact HOO']. intros j Hj. cbn [cells_size csize] in Hj.
          assert (Wj : img_w (A_OFL_HEAD + j)) by (right; left; lia).
          split; [exact Wj | apply KI; [exact Wj | unfold A_OFL_HEAD, A_STDERR; lia]]. }
        split; [do 3 eexists; exists pad; exact PS2|].
        split; [exact TS2|].
        exists bj2. split; [exact HU2|]. split; [rewrite HL2; exact HL | exact HF2']. }
      split; [lia|]. split; [exact Hpi|]. split; [exact Hp1n|].
      split; [exact R10|].
      split; [transitivity (getr regs' 18); [exact (CS 18 ltac:(unfold callee_saved; lia)) | exact K18]|].
      split; [transitivity (getr regs' 20); [exact (CS 20 ltac:(unfold callee_saved; lia)) | exact K20]|].
      split; [transitivity (getr regs' 25); [exact (CS 25 ltac:(unfold callee_saved; lia)) | exact K25]|].
      split; [transitivity (getr regs' 27); [exact (CS 27 ltac:(unfold callee_saved; lia)) | exact K27]|].
      split.
      { apply (tr_mb_bytes mem' mem2 _ _); [|exact Q8']. intros j Hj. rewrite length_le8 in Hj.
        apply KF; unfold spk, fsp, SLOT_FRAME in *; lia. }
      split.
      { apply (tr_mb_bytes mem' mem2 _ _); [|exact Q16']. intros j Hj. rewrite length_le8 in Hj.
        apply KF; unfold spk, fsp, SLOT_FRAME in *; lia. }
      apply (tr_frw g 3 _ L A regs2 mem2 md mem' (spk g 32) _ HF2);
        [unfold spk; lia | unfold spk; cbn [cells_size csize]; lia | | exact (rw_rel _ _ _ _ HR D32)].
      intros j Hj. cbn [cells_size csize] in Hj. apply KF; unfold spk, fsp, SLOT_FRAME in *; lia.
Qed.

Lemma ug_walk_cf : Hcut_cf B APIf ra (Inv_K130a4 B APIf ra empty) uC0 -> forall g i p, HC4_cf B APIf ra empty g i p.
Proof. intros HT. exact (uk4_all_cf B APIf ra empty ug_L_cf ug_L2_cf (ug_W_cf HT)). Qed.

Lemma ug_K12e3c_cf : Hcut_cf B APIf ra (Inv_K130a4 B APIf ra empty) uC0 ->
  Hcut_cf B APIf ra (Inv_K12e3c B APIf ra empty) (fun g => uafter g 24).
Proof. intros HT g c Hcap Hc. exact (ug_D_cf g (ug_W_cf HT g) (ug_walk_cf HT g) c Hcap Hc). Qed.

End W.
