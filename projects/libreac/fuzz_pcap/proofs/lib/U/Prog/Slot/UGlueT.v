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
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import Img0 Contract FrameAPI OutForm MemNorm.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog Require Import StdioModel libreac_fuzz_fopen_c
  pcap_source_next_lib pcap_source_open_c pcap_source_close_c pcap_source_next_c.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U Require Import AllocSlots AllocRoom SlotAgree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Prog.Slot Require Import PInv PTac PGlue UCut USegR PSteps UBridge
  PInvCF USROcf UContractCF.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.U.Reusable Require Import YM0b.
Import ListNotations.
Open Scope Z_scope.

(* Glue of the slot's tail: the frees after the second close (R5: free(buf), R6: free(b)). *)

(* Memory facts carried by mbyte equality. *)
Lemma tr_mb_bytes : forall (m m' : word -> option byte) a bs,
  (forall i, 0 <= i < Z.of_nat (length bs) -> mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  bytes_at rsegs m a bs -> bytes_at rsegs m' a bs.
Proof. intros m m' a bs H HB. exact (ss_bytes_mbyte rsegs m m' a bs H HB). Qed.

(* Cells in the image bytes the run writes (the stderr FILE, the open-file head): their bytes by mbyte equality,
   their writability from the image. *)
Lemma tr_img_rw : forall (m m' : word -> option byte) a cs,
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> img_w (a + i) /\ mbyte rsegs m' (a + i) = mbyte rsegs m (a + i)) ->
  rw_cells rsegs m a cs -> rw_cells rsegs m' a cs.
Proof.
  intros m m' a cs H [[Hwf Hb] (Hw1 & Hw2 & Hw3)].
  split; [split; [exact Hwf|]|].
  - apply (tr_mb_bytes m m' a (cells_bytes cs)); [|exact Hb].
    intros i Hi. rewrite cells_bytes_length in Hi by exact Hwf. exact (proj2 (H i Hi)).
  - split; [exact Hw1|]. split; [exact Hw2|]. intros i Hi.
    destruct (img_w_wr m' (a + i) (proj1 (H i Hi))) as (W & _). exact W.
Qed.

Lemma tr_errf : forall (m m' : word -> option byte),
  (forall x, img_w x -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (exists fl md, errf m fl md) -> exists fl md, errf m' fl md.
Proof.
  intros m m' H (fl & md & E1 & E2). exists fl, md. split; [|exact E2].
  apply (tr_img_rw m m' A_STDERR _); [|exact E1].
  intros i Hi. cbn [cells_size csize stderr_cells] in Hi.
  assert (W : img_w (A_STDERR + i)) by (right; right; lia).
  split; [exact W | exact (H _ W)].
Qed.

Lemma tr_ofl_empty : forall (m m' : word -> option byte),
  (forall x, img_w x -> mbyte rsegs m' x = mbyte rsegs m x) -> ofl_empty m -> ofl_empty m'.
Proof.
  intros m m' H HO. apply (tr_img_rw m m' A_OFL_HEAD _); [|exact HO].
  intros i Hi. cbn [cells_size csize] in Hi.
  assert (W : img_w (A_OFL_HEAD + i)) by (right; left; lia).
  split; [exact W | exact (H _ W)].
Qed.

(* A segment run on the normalized memory: every byte reads the same in the actual memory after it. *)
Lemma tr_rel_mb : forall (mem m' : word -> option byte), ro_agree rsegs mem ->
  mem_rel rsegs m' (normalize rsegs mem) -> forall x, mbyte rsegs m' x = mbyte rsegs mem x.
Proof.
  intros mem m' HRO HR x.
  rewrite (mbyte_rel rsegs m' (normalize rsegs mem) x HR).
  symmetry. exact (mbyte_rel rsegs mem (normalize rsegs mem) x (mem_rel_normalize rsegs mem HRO)).
Qed.

Lemma tr_rel_stdio : forall (mem m' : word -> option byte), ro_agree rsegs mem ->
  mem_rel rsegs m' (normalize rsegs mem) -> stdio_ok mem -> stdio_ok m'.
Proof.
  intros mem m' HRO HR (S1 & S2 & S3).
  pose proof (tr_rel_mb mem m' HRO HR) as E.
  split; [|split]; (eapply tr_mb_bytes; [intros i _; apply E|]); assumption.
Qed.

(* The stderr FILE's mode field (A_STDERR + 136 = 0x1eac0) holds md, 0 or 0xffffffff: the output invariant. *)
Lemma GI_of_errf : forall m fl md j, errf m fl md -> GI j m.
Proof.
  intros m fl md j ([[_ Hb] _] & _ & Hmd).
  assert (E : stderr_cells fl md = firstn 19 (stderr_cells fl md) ++ [C4 (wz md)] ++ skipn 20 (stderr_cells fl md))
    by reflexivity.
  rewrite E in Hb. rewrite !cells_bytes_app in Hb.
  apply bytes_at_app in Hb as [_ Hb]. apply bytes_at_app in Hb as [Hb _].
  cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  assert (L : A_STDERR + Z.of_nat (length (cells_bytes (firstn 19 (stderr_cells fl md)))) = (symaddr (Symbols.Ubsan.s___stderr_FILE + 0x88)%Z))
    by (unfold A_STDERR; reflexivity).
  rewrite L in Hb. unfold GI, wz in *.
  destruct Hmd as [-> | ->]; [left | right]; exact Hb.
Qed.

(* Facts carried across a reader call by the bytes it keeps: open/close write the open-file head (so the stderr
   FILE stays), next writes the stderr FILE (so the open-file head stays). *)
Lemma tr_errf_o : forall (m m' : word -> option byte),
  (forall x, img_w x -> ~ (A_OFL_HEAD <= x < A_OFL_HEAD + 8) -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (exists fl md, errf m fl md) -> exists fl md, errf m' fl md.
Proof.
  intros m m' H (fl & md & E1 & E2). exists fl, md. split; [|exact E2].
  apply (tr_img_rw m m' A_STDERR _); [|exact E1].
  intros i Hi. cbn [cells_size csize stderr_cells] in Hi.
  assert (W : img_w (A_STDERR + i)) by (right; right; lia).
  split; [exact W | apply H; [exact W | unfold A_STDERR, A_OFL_HEAD; lia]].
Qed.

Lemma tr_ofl_s : forall (m m' : word -> option byte) h,
  (forall x, img_w x -> ~ (A_STDERR <= x < A_STDERR + 232) -> mbyte rsegs m' x = mbyte rsegs m x) ->
  ofl_one m h -> ofl_one m' h.
Proof.
  intros m m' h H HO. apply (tr_img_rw m m' A_OFL_HEAD _); [|exact HO].
  intros i Hi. cbn [cells_size csize] in Hi.
  assert (W : img_w (A_OFL_HEAD + i)) by (right; left; lia).
  split; [exact W | apply H; [exact W | unfold A_STDERR, A_OFL_HEAD; lia]].
Qed.

Lemma tr_q64 : forall (m m' : word -> option byte) a v,
  (forall x, a <= x < a + 8 -> mbyte rsegs m' x = mbyte rsegs m x) -> q64 m a v -> q64 m' a v.
Proof.
  intros m m' a v H Q. unfold q64 in *. apply (tr_mb_bytes m m' a _); [|exact Q].
  intros i Hi. rewrite length_le8 in Hi. apply H. lia.
Qed.

(* The f cell (the stream) of a source struct. *)
Lemma tr_f0 : forall m a f sw olen vtag vid pad,
  rw_cells rsegs m a (PS.ps_cells f sw olen vtag vid pad) -> bytes_at rsegs m a (le8 f).
Proof.
  intros m a f sw olen vtag vid pad H. apply ss_cells_bytes in H.
  unfold PS.ps_cells in H. cbn [cells_bytes cbytes] in H.
  exact (proj1 (proj1 (bytes_at_app rsegs m a _ _) H)).
Qed.

(* The registers after a segment that sets ra and a0-a3 only. *)
Definition tregs (regs : bvmap 5 word) (r1 r10 r11 r12 r13 : word) : bvmap 5 word :=
  mkR r1 (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8)
    (getr regs 9) r10 r11 r12 r13 (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
    (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
    (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).

(* A segment that writes no memory: the actual memory after it equals the one before at every address. *)
Lemma tr_same : forall mem mem', ro_agree rsegs mem -> mem_rel rsegs mem' (normalize rsegs mem) ->
  ro_same rsegs mem mem' -> munch [] mem mem' /\ wmono rsegs mem mem'.
Proof.
  intros mem mem' HRO HR HS.
  assert (E : forall x, mem' x = mem x).
  { apply (mem_unchanged_rel rsegs mem (normalize rsegs mem) mem' (normalize rsegs mem));
      [exact (mem_rel_normalize rsegs mem HRO) | exact HR | exact HS | reflexivity]. }
  split; [intros x _; apply E | apply ss_wmono_eq; exact E].
Qed.

(* TKEEP across a segment that writes no memory. *)
Lemma tr_TK0 : forall g b buf regs regs' m m', munch [] m m' -> wmono rsegs m m' ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 -> TKEEP g b buf regs m -> TKEEP g b buf regs' m'.
Proof.
  intros g b buf regs regs' m m' MU WM E8 E9 E26 E27
    ((H8 & H9 & H26 & ((S1 & S2 & S3) & (G1 & gv & G2) & (fl & md & E1 & E2) & Q0 & QL) & Q8 & HB & Q24) & H27 &
     (bj & HU & HL)).
  assert (T : forall a bs, bytes_at rsegs m a bs -> bytes_at rsegs m' a bs)
    by (intros a bs H; exact (bytes_at_transport rsegs [] m m' a bs H MU I)).
  split; [|split; [rewrite E27; exact H27|]].
  - split; [rewrite E8; exact H8|]. split; [rewrite E9; exact H9|]. split; [rewrite E26; exact H26|].
    split; [|split; [exact (T _ _ Q8)|]; split; [exact (T _ _ HB) | exact (T _ _ Q24)]].
    split; [split; [exact (T _ _ S1)|]; split; [exact (T _ _ S2) | exact (T _ _ S3)]|].
    split; [split; [exact (T _ _ G1) | exists gv; exact (T _ _ G2)]|].
    split; [exists fl, md; split; [exact (rw_cells_transport rsegs [] m m' _ _ E1 MU WM I) | exact E2]|].
    split; [exact (T _ _ Q0) | exact (T _ _ QL)].
  - exists bj. split; [exact (Arr.u8arr_transport rsegs [] m m' buf bj HU MU WM I) | exact HL].
Qed.

(* TKEEP across a call: the kept registers, the frame bytes below the source struct, g_file_len/g_file, and the
   facts the call's step gives. *)
Lemma tr_TK : forall g b buf regs regs' m m',
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 26 = getr regs 26 ->
  getr regs' 27 = getr regs 27 ->
  (forall x, fsp g <= x < fsp g + 48 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  (forall x, G_FILE_LEN <= x < G_FILE_LEN + 16 -> mbyte rsegs m' x = mbyte rsegs m x) ->
  stdio_ok m' -> guard_ok m' -> (exists fl md, errf m' fl md) -> bytes_at rsegs m' b (uF g) ->
  BUFC m' buf (ubn g) -> TKEEP g b buf regs m -> TKEEP g b buf regs' m'.
Proof.
  intros g b buf regs regs' m m' E8 E9 E26 E27 KF KG S G E HB HU
    ((H8 & H9 & H26 & (_ & _ & _ & Q0 & QL) & Q8 & _ & Q24) & H27 & _).
  split; [|split; [rewrite E27; exact H27 | exact HU]].
  split; [rewrite E8; exact H8|]. split; [rewrite E9; exact H9|]. split; [rewrite E26; exact H26|].
  split; [|split; [|split; [exact HB|]]].
  - split; [exact S|]. split; [exact G|]. split; [exact E|].
    split; [apply (tr_q64 m m'); [intros x Hx; apply KF; unfold spk in Hx; lia | exact Q0]|].
    apply (tr_q64 m m'); [intros x Hx; apply KG; lia | exact QL].
  - apply (tr_q64 m m'); [intros x Hx; apply KG; lia | exact Q8].
  - apply (tr_q64 m m'); [intros x Hx; apply KF; unfold spk in Hx; lia | exact Q24].
Qed.

Lemma tr_ud : forall g, 0 <= ud g < 256.
Proof. intros g. unfold ud. destruct (g_in g) as [|d l]; [lia|]. apply ss_bz_range. Qed.

Lemma tr_swz : forall g, uswz g = 0 \/ uswz g = 1.
Proof. intros g. unfold uswz, PS.pcap_sw. destruct (PS.pcap_magic (uF g) =? 0xD4C3B2A1); [right | left]; reflexivity. Qed.

(* The output of the call from 24 on the open stream h. *)
Lemma tr_C0 : forall g h, h <> 0 -> uC0 g = UN.psn_out h (uswz g =? 1) (uF g) (ucap g) 24 ++ [].
Proof.
  intros g h Hh. rewrite app_nil_r, psn_out_UP. unfold PN.psn_out.
  destruct (Z.eqb_spec h 0) as [E|E]; [contradiction|]. reflexivity.
Qed.

Lemma tr_room : forall b0 hb n, slot_room b0 -> (length hb <= 16)%nat -> 0 <= hb_bytes hb <= 2 ^ 30 ->
  0 <= n <= 2 ^ 22 -> room_slots (sb_hb b0 hb) n.
Proof.
  intros b0 hb n (HL & HB & HC) Hlen HS Hn.
  unfold room_slots, sb_hb. cbn [sb_live sb_bytes sb_cap].
  split; [lia|]. split; [lia|].
  apply (CAPOK_mono CAPMAX (sb_cap b0) (2 ^ 40) _ (2 ^ 22) n); [lia | lia | lia | exact CAPOK_small].
Qed.

Section T.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AllocAPI B.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf SH SK ra empty.

Definition HCT (X : ghost -> config -> Prop) : Prop :=
  forall g c, X g c -> SRO (ms_segs B) c [] (Post_o B APIf ra g).

Lemma ug_ret_ok : forall z, 0 <= z < 2 ^ 64 -> z mod 2 = 0 -> YK0s.ret_ok (Z_to_bv 64 z).
Proof. intros z Hz He. apply ret_ok_even. rewrite unsigned_lit by lia. exact He. Qed.

(* R6: 0x130cc -> free(b) -> 0x130d4. *)
Lemma ug_R6 : HCT (Inv_K1310c B APIf ra empty) -> HCT (Inv_K13104 B APIf ra empty).
Proof.
  intros H g c (b & Hgood & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z) 4 [(b, un g)] _ c [] (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (H8 & Hstd & Hgd & Herr & Hofl).
  pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (_ & _ & _ & _ & HRO).
  apply (run_to B APIf ra empty FF g 4 [(b, un g)] L A regs mem md (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z))
    (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
       (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 8) (getr regs 11) (getr regs 12) (getr regs 13)
       (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
       (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
       (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)) fp_regs (Z_to_bv 64 (symaddr Symbols.Ubsan.s_free)) fp_csr None
       (normalize rsegs mem) (seg_rom rsegs))
    [] (fun c' => SRO (ms_segs B) c' [] (Post_o B APIf ra g)) (Post_o B APIf ra g) HF HP).
  - rewrite ss_mkR_of. exact (ubs_R6_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr (normalize rsegs mem)).
  - intros ms ->. do 3 eexists. split; [reflexivity|].
    split; [exists []; split; [apply munch_refl|]; split; [apply wmono_refl | intros x _ O; exfalso; exact (O I)]|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ XR HR HF'.
    injection HQ as ER Epc Em. subst R pc' m0'.
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    assert (G10 : getr regs' 10 = wz b) by (rewrite (ss_getr_eqv _ _ 10 XR); exact H8).
    pose proof (tr_rel_mb mem m' HRO HR) as EM.
    rewrite <- (ss_free_pc B APIf ra empty FF).
    apply (ss_free_step B APIf ra empty FF g 4 [] b (un g) [] L A regs' m' md [] (Post_o B APIf ra g) HF' HP).
    + rewrite G1. apply ug_ret_ok; lia.
    + exact G10.
    + exact (tr_rel_stdio mem m' HRO HR Hstd).
    + intros L2 A2 regs2 mem2 md2 HF2 HP2 RP2 FRM2 IMG2 STD2 GRD2.
      rewrite G1. apply H. exists 4.
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z) 4 [] _ L2 A2 regs2 mem2 md2 Hfrm HF2 HP2).
      rewrite (sg_segs B APIf ra empty FF) in IMG2.
      assert (IM : forall x, img_w x -> mbyte rsegs mem2 x = mbyte rsegs mem x)
        by (intros x Hx; rewrite (IMG2 x Hx); apply EM).
      split; [exact STD2|]. split; [exact GRD2|].
      split; [exact (tr_errf mem mem2 IM Herr) | exact (tr_ofl_empty mem mem2 IM Hofl)].
  - intros c' Hc. exact Hc.
Qed.

(* R5: 0x130bc (the call on the closed reader answered -1) -> free(buf) -> 0x130cc. *)
Lemma ug_R5 : HCT (Inv_K13104 B APIf ra empty) -> HCT (Inv_K130f4 B APIf ra empty).
Proof.
  intros H g c (b & buf & Hgood & HC).
  apply (cut_open B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z) 4 [(b, un g); (buf, ubn g)] _ c [] (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (H10 & ((H8 & H9 & H26 & (Hstd & Hgd & Herr & Q0 & QL) & QG & HBF & Q24) & H27
    & HBUF) & Hofl).
  pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & HRO).
  assert (USP : bv_unsigned (getr regs 2) = fsp g)
    by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
  assert (Q24n : bytes_at rsegs (normalize rsegs mem) (fsp g + 24) (le8 (wz buf)))
    by (apply bytes_at_normalize; [exact HRO | exact Q24]).
  apply (run_to B APIf ra empty FF g 4 [(b, un g); (buf, ubn g)] L A regs mem md (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z))
    (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z)) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
       (getr regs 7) (getr regs 8) (getr regs 9) (wz buf) (wz (-1)) (getr regs 12) (getr regs 13)
       (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
       (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
       (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)) fp_regs (Z_to_bv 64 (symaddr Symbols.Ubsan.s_free)) fp_csr None
       (normalize rsegs mem) (seg_rom rsegs))
    [] (fun c' => SRO (ms_segs B) c' [] (Post_o B APIf ra g)) (Post_o B APIf ra g) HF HP).
  - rewrite ss_mkR_of. exact (ubs_R5_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr (normalize rsegs mem)
      (fsp g) buf USP H10 Q24n).
  - intros ms ->. do 3 eexists. split; [reflexivity|].
    split; [exists []; split; [apply munch_refl|]; split; [apply wmono_refl | intros x _ O; exfalso; exact (O I)]|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ XR HR HF'.
    injection HQ as ER Epc Em. subst R pc' m0'.
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    assert (G10 : getr regs' 10 = wz buf) by (rewrite (ss_getr_eqv _ _ 10 XR); reflexivity).
    assert (G8 : getr regs' 8 = wz b) by (rewrite (ss_getr_eqv _ _ 8 XR); exact H8).
    pose proof (tr_rel_mb mem m' HRO HR) as EM.
    rewrite <- (ss_free_pc B APIf ra empty FF).
    apply (ss_free_step B APIf ra empty FF g 4 [(b, un g)] buf (ubn g) [] L A regs' m' md [] (Post_o B APIf ra g)
      HF' HP).
    + rewrite G1. apply ug_ret_ok; lia.
    + exact G10.
    + exact (tr_rel_stdio mem m' HRO HR Hstd).
    + intros L2 A2 regs2 mem2 md2 HF2 HP2 RP2 FRM2 IMG2 STD2 GRD2.
      rewrite G1. apply H. exists b. split; [exact Hgood|].
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z) 4 [(b, un g)] _ L2 A2 regs2 mem2 md2 Hfrm HF2 HP2).
      rewrite (sg_segs B APIf ra empty FF) in IMG2.
      assert (IM : forall x, img_w x -> mbyte rsegs mem2 x = mbyte rsegs mem x)
        by (intros x Hx; rewrite (IMG2 x Hx); apply EM).
      split; [transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia)) | exact G8]|].
      split; [exact STD2|]. split; [exact GRD2|].
      split; [exact (tr_errf mem mem2 IM Herr) | exact (tr_ofl_empty mem mem2 IM Hofl)].
  - intros c' Hc. exact Hc.
Qed.

Hypothesis HNEXT : forall fx0 : FPState, pcap_source_next_contract (fx := fx0).
Hypothesis HCLOSE : forall fx0 : FPState, pcap_source_close_contract (fx := fx0) B (APIf rc).
Hypothesis HOPEN : forall fx0 : FPState, pcap_source_open_contract (fx := fx0) B (APIf rc).

Lemma tr_fr : forall g km hb L A regs mem md, FR B APIf ra empty g km hb L A regs mem md ->
  bv_unsigned (getr regs 2) = fsp g /\ fsp g mod 16 = 0 /\ 65536 <= fsp g /\ g_S g = fsp g + 176 /\
  g_S g <= 2 ^ 47.
Proof.
  intros g km hb L A regs mem md HF.
  destruct (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & _).
  unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *.
  split; [rewrite HSP; apply unsigned_lit; lia|]. split; [exact H16|]. lia.
Qed.

Lemma tr_un : forall g, GV B empty g -> 0 <= un g < 2 ^ 26.
Proof.
  intros g (Hn & _). unfold un, zlen, uF. unfold g_n in Hn.
  destruct (g_in g) as [|x l]; cbn [tl length] in *; lia.
Qed.

(* A heap block of the slot holds some bytes it can write: the buffer cell after a call that may write it. *)
Lemma tr_bufc : forall g km hb L A regs mem md a k,
  FR B APIf ra empty g km hb L A regs mem md -> Permutation (blocks L A) (hb ++ blocks (g_L g) (g_A g)) ->
  In (a, k) hb -> 0 <= k -> BUFC mem a k.
Proof.
  intros g km hb L A regs mem md a k HF HP Hin Hk.
  destruct (ss_hb_blk B APIf ra empty FF g km hb L A regs mem md a k HF HP Hin) as (W & A1 & A2 & _).
  pose proof (@YM05.alloc_ceiling_lt rc) as HAC.
  rewrite (sg_segs B APIf ra empty FF) in W.
  assert (ST : Frame.stk rsegs mem a (a + k)).
  { split; [lia|]. split; [lia|]. intros x Hx.
    destruct (W (x - a) ltac:(lia)) as (W1 & (v & Hv) & _).
    replace (a + (x - a)) with x in W1, Hv by lia.
    split; [exact W1|]. exists v. unfold Mem.mrd, Mem.wa. rewrite Hv. reflexivity. }
  destruct (stk_carve rsegs mem a (a + k) (Z.to_nat k) ST ltac:(lia)) as [_ (junk & HJ)].
  replace (a + k - Z.of_nat (Z.to_nat k)) with a in HJ by lia.
  exists junk. split; [exact (Arr.u8arr_of_rw_cells rsegs mem a _ junk HJ)|].
  destruct HJ as [[Hwf _] _]. cbn [cells_wf cell_wf] in Hwf. destruct Hwf as [Hl _]. lia.
Qed.

(* Two blocks of the slot have different addresses. *)
Lemma tr_neq3 : forall g km x kx y ky z kz L A regs mem md,
  FR B APIf ra empty g km [(x, kx); (y, ky); (z, kz)] L A regs mem md ->
  Permutation (blocks L A) ([(x, kx); (y, ky); (z, kz)] ++ blocks (g_L g) (g_A g)) -> x <> z.
Proof.
  intros g km x kx y ky z kz L A regs mem md HF HP.
  pose proof HF as (_ & _ & _ & _ & _ & _ & _ & _ & HMR & _).
  destruct (ss_alloc B APIf ra empty FF) as (_ & _ & _ & _ & _ & _ & _ & _ & ND & _).
  pose proof (proj1 (stdpp.base.NoDup_ListNoDup _) (ND L A mem md HMR)) as Hnd.
  apply (Permutation_NoDup (Permutation_map fst HP)) in Hnd.
  cbn [map app fst] in Hnd. apply NoDup_cons_iff in Hnd as [Hn _].
  intros E. apply Hn. right. left. symmetry. exact E.
Qed.

(* R4: 0x130a8 (after the second close) -> pcap_source_next on the closed reader (h = 0: answer -1, no output)
   -> 0x130bc. *)
Lemma ug_R4 : HCT (Inv_K130f4 B APIf ra empty) -> HCT (Inv_K130e0 B APIf ra empty).
Proof.
  intros H g c (b & buf & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HTK & Hofl & HPSC).
  destruct HPSC as (lol & lvt & lvid & pad & HPS).
  pose proof HTK as ((_ & E9 & _ & (_ & _ & (fl & mdv & HEF) & _) & _ & _ & Q24) & _ & (bj & HU & HL)).
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (sg_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (tr_fr g _ _ L A regs mem md HF) as (USP & H16 & HFS & ES & HS47).
  destruct (ss_hb_blk B APIf ra empty FF g _ _ L A regs mem md b (un g) HF HP ltac:(left; reflexivity))
    as (_ & Hb4 & _).
  assert (Q24n : bytes_at rsegs (normalize rsegs mem) (fsp g + 24) (le8 (wz buf)))
    by (apply bytes_at_normalize; [exact HMI | exact Q24]).
  apply (ss_kA_run_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z)) mem md
    (fun R pc' m' => R = tregs regs (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z)) (wz (fsp g + 48)) (wz buf) (getr regs 9) (wz 0) /\
       pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next) /\ m' = normalize rsegs mem) _ (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (sg_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_R4_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (fsp g) buf USP Q24n)|].
    intros ms ->. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m' regs' mem' (-> & -> & ->) XR HR HS.
    destruct (tr_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 4 [(b, un g); (buf, ubn g)] L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 4 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); reflexivity | rewrite (ss_getr_eqv _ _ 3 XR); reflexivity
        | rewrite (ss_getr_eqv _ _ 4 XR); reflexivity | exact MU | exact WM | intros lo hi y [] ]. }
    pose proof (tr_TK0 g b buf regs regs' mem mem' MU WM ltac:(rewrite (ss_getr_eqv _ _ 8 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 9 XR); reflexivity) ltac:(rewrite (ss_getr_eqv _ _ 26 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 27 XR); reflexivity) HTK) as TK'.
    pose proof TK' as ((_ & _ & _ & (HSTD' & _) & _ & HBF' & _) & _).
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    apply (ps_next_step (fx := fx') B APIf ra empty FF (HNEXT fx') g 4 [(b, un g); (buf, ubn g)] [(b, un g)] L A
      regs' mem' md (spk g 48) buf (ucap g) 0 0 (uswz g) b 24 fl mdv lol lvt lvid (wz 0) (wz 0) (wz 0) pad bj (uF g)
      [] (Post_o B APIf ra g) FR' HP Hfrm).
    + rewrite G1. apply ug_ret_ok; lia.
    + rewrite (ss_getr_eqv _ _ 10 XR). reflexivity.
    + rewrite (ss_getr_eqv _ _ 11 XR). reflexivity.
    + rewrite (ss_getr_eqv _ _ 12 XR). exact E9.
    + rewrite (ss_getr_eqv _ _ 13 XR). reflexivity.
    + unfold spk. lia.
    + unfold spk. lia.
    + unfold spk. lia.
    + exact (rw_cells_transport rsegs [] mem mem' _ _ HPS MU WM I).
    + apply perm_swap.
    + exact (Arr.u8arr_transport rsegs [] mem mem' buf bj HU MU WM I).
    + exact HL.
    + pose proof (tr_ud g). unfold ucap. lia.
    + intros N. exfalso. exact (N eq_refl).
    + intros N. exfalso. exact (N eq_refl).
    + destruct HEF as (E1 & E2). split; [exact (rw_cells_transport rsegs [] mem mem' _ _ E1 MU WM I) | exact E2].
    + intros regs2 mem2 Ft fc' mdv' Hfc _ FR2 RP2 KF2 KH2 KI2 KS2 HE2 HG2 H02 _.
      rewrite (sg_segs B APIf ra empty FF) in KF2, KH2, KI2.
      rewrite G1. apply H. exists b, buf. split; [exact Hgood|].
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc') g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z) 4 _ _ L A regs2 mem2 md Hfc FR2 HP).
      split; [exact (H02 eq_refl)|].
      split; [|exact (tr_ofl_s mem' mem2 0 KI2 (rw_cells_transport rsegs [] mem mem' _ _ Hofl MU WM I))].
      apply (tr_TK g b buf regs' regs2 mem' mem2).
      * exact (RP2 8 ltac:(unfold callee_saved; lia)).
      * exact (RP2 9 ltac:(unfold callee_saved; lia)).
      * exact (RP2 26 ltac:(unfold callee_saved; lia)).
      * exact (RP2 27 ltac:(unfold callee_saved; lia)).
      * intros x Hx. apply KF2; unfold spk; lia.
      * intros x Hx. apply KI2; [apply img_w_iff; right; left; unfold G_FILE_LEN in Hx; lia
                                | unfold A_STDERR, G_FILE_LEN in *; lia].
      * exact (KS2 HSTD').
      * exact HG2.
      * exists fl, mdv'. exact HE2.
      * apply (tr_mb_bytes mem' mem2 b _); [|exact HBF'].
        intros i Hi. apply (KH2 b (un g) i); [left; reflexivity | lia | unfold un, zlen; lia].
      * apply (tr_bufc g 4 [(b, un g); (buf, ubn g)] L A regs2 mem2 md buf (ubn g) FR2 HP);
          [right; left; reflexivity | unfold ubn; lia].
      * exact TK'.
Qed.

(* R3: 0x1309c (the call from 24 answered the first answer again: a0 = s11) -> pcap_source_close (the stream h
   freed) -> 0x130a8. *)
Lemma ug_R3 : HCT (Inv_K130e0 B APIf ra empty) -> HCT (Inv_K130d4 B APIf ra empty).
Proof.
  intros H g c (b & buf & h & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & E10 & HTK & HMS & HOO
    & HPSC).
  destruct HPSC as (lol & lvt & lvid & pad & HPS).
  pose proof HTK as (_ & E27 & _).
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (sg_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (tr_fr g _ _ L A regs mem md HF) as (USP & H16 & HFS & ES & HS47).
  apply (ss_kA_run_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z)) mem md
    (fun R pc' m' => R = tregs regs (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z)) (wz (fsp g + 48)) (getr regs 11) (getr regs 12) (getr regs 13) /\
       pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_close) /\ m' = normalize rsegs mem) _ (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (sg_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_R3_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (fsp g) USP ltac:(rewrite E10, E27; reflexivity))|].
    intros ms ->. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m' regs' mem' (-> & -> & ->) XR HR HS.
    destruct (tr_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 4 [(b, un g); (buf, ubn g); (h, 1304)] L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 4 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); reflexivity | rewrite (ss_getr_eqv _ _ 3 XR); reflexivity
        | rewrite (ss_getr_eqv _ _ 4 XR); reflexivity | exact MU | exact WM | intros lo hi y [] ]. }
    pose proof (tr_TK0 g b buf regs regs' mem mem' MU WM ltac:(rewrite (ss_getr_eqv _ _ 8 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 9 XR); reflexivity) ltac:(rewrite (ss_getr_eqv _ _ 26 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 27 XR); reflexivity) HTK) as TK'.
    pose proof TK' as ((_ & _ & _ & (HSTD' & _ & HER' & _) & _ & _ & _) & _).
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    apply (ps_close_step (fx := fx') B APIf ra empty FF (HCLOSE fx') g 4 [(b, un g); (buf, ubn g)] h [] L A regs'
      mem' md (spk g 48) (wz (uswz g)) lol lvt lvid pad b (uF g) (upos g (uQ g 24)) [] (Post_o B APIf ra g) FR' HP).
    + rewrite G1. apply ug_ret_ok; lia.
    + rewrite (ss_getr_eqv _ _ 10 XR). reflexivity.
    + unfold spk. lia.
    + unfold spk. lia.
    + unfold spk. lia.
    + exact (rw_cells_transport rsegs [] mem mem' _ _ HPS MU WM I).
    + cbn [app]. left. reflexivity.
    + exact (mstl_transport [] mem mem' h b (uF g) _ _ _ HMS MU WM I I).
    + exact (rw_cells_transport rsegs [] mem mem' _ _ HOO MU WM I).
    + exact HSTD'.
    + intros L2 A2 regs2 mem2 md2 FR2 HP2 RP2 KF2 _ KI2 HPS2 HOE2 HSTD2 HG2 HBF2.
      rewrite (sg_segs B APIf ra empty FF) in KF2, KI2.
      rewrite G1. apply H. exists b, buf. split; [exact Hgood|].
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z) 4 _ _ L2 A2 regs2 mem2 md2 Hfrm FR2 HP2).
      split; [|split; [exact HOE2 | exists lol, lvt, lvid, pad; exact HPS2]].
      apply (tr_TK g b buf regs' regs2 mem' mem2).
      * exact (RP2 8 ltac:(unfold callee_saved; lia)).
      * exact (RP2 9 ltac:(unfold callee_saved; lia)).
      * exact (RP2 26 ltac:(unfold callee_saved; lia)).
      * exact (RP2 27 ltac:(unfold callee_saved; lia)).
      * intros x Hx. apply KF2; unfold spk; lia.
      * intros x Hx. apply KI2; [apply img_w_iff; right; left; unfold G_FILE_LEN in Hx; lia
                                | unfold A_OFL_HEAD, G_FILE_LEN in *; lia].
      * exact HSTD2.
      * exact HG2.
      * exact (tr_errf_o mem' mem2 KI2 HER').
      * exact HBF2.
      * apply (tr_bufc g 4 [(b, un g); (buf, ubn g)] L2 A2 regs2 mem2 md2 buf (ubn g) FR2 HP2);
          [right; left; reflexivity | unfold ubn; lia].
      * exact TK'.
Qed.

(* R2: 0x13084 (the reopen answered 0) -> pcap_source_next from 24 on the open stream h, without ts (output
   uC0 g) -> 0x1309c. *)
Lemma ug_R2 : HCT (Inv_K130d4 B APIf ra empty) -> Hcut_o B APIf ra (Inv_K130bc B APIf ra empty) uC0.
Proof.
  intros H g c (b & buf & h & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & E10 & HTK & HPSC & HMS
    & HOO).
  destruct HPSC as (pad & HPS).
  pose proof HTK as ((_ & E9 & _ & (_ & _ & (fl & mdv & HEF) & _) & _ & _ & Q24) & _ & (bj & HU & HL)).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (sg_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (tr_fr g _ _ L A regs mem md HF) as (USP & H16 & HFS & ES & HS47).
  destruct (ss_hb_blk B APIf ra empty FF g _ _ L A regs mem md h 1304 HF HP
    ltac:(right; right; left; reflexivity)) as (_ & Hh4 & _).
  assert (Hhn : h <> 0) by lia.
  pose proof (tr_neq3 g 4 b (un g) buf (ubn g) h 1304 L A regs mem md HF HP) as Hbh.
  assert (Q24n : bytes_at rsegs (normalize rsegs mem) (fsp g + 24) (le8 (wz buf)))
    by (apply bytes_at_normalize; [exact HMI | exact Q24]).
  rewrite (tr_C0 g h Hhn).
  apply (ss_kA_run_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z)) mem md
    (fun R pc' m' => R = tregs regs (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z)) (wz (fsp g + 48)) (wz buf) (getr regs 9) (wz 0) /\
       pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next) /\ m' = normalize rsegs mem) _ (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (sg_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_R2_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (fsp g) buf USP E10 Q24n)|].
    intros ms ->. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m' regs' mem' (-> & -> & ->) XR HR HS.
    destruct (tr_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 4 [(b, un g); (buf, ubn g); (h, 1304)] L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 4 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); reflexivity | rewrite (ss_getr_eqv _ _ 3 XR); reflexivity
        | rewrite (ss_getr_eqv _ _ 4 XR); reflexivity | exact MU | exact WM | intros lo hi y [] ]. }
    pose proof (tr_TK0 g b buf regs regs' mem mem' MU WM ltac:(rewrite (ss_getr_eqv _ _ 8 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 9 XR); reflexivity) ltac:(rewrite (ss_getr_eqv _ _ 26 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 27 XR); reflexivity) HTK) as TK'.
    pose proof TK' as ((_ & _ & _ & (HSTD' & _) & _ & HBF' & _) & _).
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    apply (ps_next_step (fx := fx') B APIf ra empty FF (HNEXT fx') g 4 [(b, un g); (buf, ubn g); (h, 1304)]
      [(b, un g); (h, 1304)] L A regs' mem' md (spk g 48) buf (ucap g) 0 h (uswz g) b 24 fl mdv (wz 0) (wz 0) (wz 0)
      (wz 0) (wz 0) (wz 0) pad bj (uF g) [] (Post_o B APIf ra g) FR' HP Hfrm).
    + rewrite G1. apply ug_ret_ok; lia.
    + rewrite (ss_getr_eqv _ _ 10 XR). reflexivity.
    + rewrite (ss_getr_eqv _ _ 11 XR). reflexivity.
    + rewrite (ss_getr_eqv _ _ 12 XR). exact E9.
    + rewrite (ss_getr_eqv _ _ 13 XR). reflexivity.
    + unfold spk. lia.
    + unfold spk. lia.
    + unfold spk. lia.
    + exact (rw_cells_transport rsegs [] mem mem' _ _ HPS MU WM I).
    + apply perm_swap.
    + exact (Arr.u8arr_transport rsegs [] mem mem' buf bj HU MU WM I).
    + exact HL.
    + pose proof (tr_ud g). unfold ucap. lia.
    + intros N. exfalso. exact (N eq_refl).
    + intros _. split; [right; left; reflexivity|]. split; [left; reflexivity|].
      split; [exact (mstl_transport [] mem mem' h b (uF g) _ _ _ HMS MU WM I I)|].
      split; [exact (tr_swz g) | exact (proj2 (tr_un g HGV))].
    + destruct HEF as (E1 & E2). split; [exact (rw_cells_transport rsegs [] mem mem' _ _ E1 MU WM I) | exact E2].
    + intros regs2 mem2 Ft fc' mdv' Hfc _ FR2 RP2 KF2 KH2 KI2 KS2 HE2 HG2 _ H12.
      destruct (H12 Hhn) as (R10 & MS2 & PS2 & _).
      rewrite psn_q_UP, res_of_UP in R10. rewrite psn_q_UP, pos_of_UP in MS2.
      rewrite (sg_segs B APIf ra empty FF) in KF2, KH2, KI2.
      rewrite G1. apply H. exists b, buf, h. split; [exact Hgood|].
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc') g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z) 4 _ _ L A regs2 mem2 md Hfc FR2 HP).
      split; [exact R10|].
      split; [|split; [exact MS2|]; split;
        [exact (tr_ofl_s mem' mem2 h KI2 (rw_cells_transport rsegs [] mem mem' _ _ HOO MU WM I))
        | do 3 eexists; exists pad; exact PS2]].
      apply (tr_TK g b buf regs' regs2 mem' mem2).
      * exact (RP2 8 ltac:(unfold callee_saved; lia)).
      * exact (RP2 9 ltac:(unfold callee_saved; lia)).
      * exact (RP2 26 ltac:(unfold callee_saved; lia)).
      * exact (RP2 27 ltac:(unfold callee_saved; lia)).
      * intros x Hx. apply KF2; unfold spk; lia.
      * intros x Hx. apply KI2; [apply img_w_iff; right; left; unfold G_FILE_LEN in Hx; lia
                                | unfold A_STDERR, G_FILE_LEN in *; lia].
      * exact (KS2 HSTD').
      * exact HG2.
      * exists fl, mdv'. exact HE2.
      * apply (tr_mb_bytes mem' mem2 b _); [|exact HBF'].
        intros i Hi. apply (KH2 b (un g) i); [left; reflexivity | exact Hbh | unfold un, zlen; lia].
      * apply (tr_bufc g 4 [(b, un g); (buf, ubn g); (h, 1304)] L A regs2 mem2 md buf (ubn g) FR2 HP);
          [right; left; reflexivity | unfold ubn; lia].
      * exact TK'.
Qed.

(* R1: 0x1306c (the reader closed: its f cell is 0) -> pcap_source_open of the file again (good: the stream h at
   24) -> 0x13084. The open step's 16 bytes at G_FILE_LEN: the length (ENV) and the copy b (WKEEP). *)
Lemma ug_R1 : Hcut_o B APIf ra (Inv_K130bc B APIf ra empty) uC0 -> Hcut_o B APIf ra (Inv_K130a4 B APIf ra empty) uC0.
Proof.
  intros H g c (b & buf & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HTK & Hofl & HPSC).
  destruct HPSC as (lol & lvt & lvid & pad & HPS).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & HSR & _).
  unfold MI in HMI. rewrite (sg_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (tr_fr g _ _ L A regs mem md HF) as (USP & H16 & HFS & ES & HS47).
  assert (F0n : bytes_at rsegs (normalize rsegs mem) (fsp g + 48) (le8 (wz 0)))
    by (apply bytes_at_normalize; [exact HMI | exact (tr_f0 _ _ _ _ _ _ _ _ HPS)]).
  apply (ss_kA_run_o B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z)) mem md
    (fun R pc' m' => R = tregs regs (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z)) (wz (fsp g + 48)) (wz (symaddr (Symbols.Ubsan.Sec.s_rodata + 0xe9)%Z)) (getr regs 12) (getr regs 13) /\
       pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_open) /\ m' = normalize rsegs mem) _ (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (sg_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_R1_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (fsp g) USP F0n)|].
    intros ms ->. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m' regs' mem' (-> & -> & ->) XR HR HS.
    destruct (tr_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 3 [(b, un g); (buf, ubn g)] L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); reflexivity | rewrite (ss_getr_eqv _ _ 3 XR); reflexivity
        | rewrite (ss_getr_eqv _ _ 4 XR); reflexivity | exact MU | exact WM | intros lo hi y [] ]. }
    pose proof (tr_TK0 g b buf regs regs' mem mem' MU WM ltac:(rewrite (ss_getr_eqv _ _ 8 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 9 XR); reflexivity) ltac:(rewrite (ss_getr_eqv _ _ 26 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 27 XR); reflexivity) HTK) as TK'.
    pose proof TK' as ((_ & _ & _ & (HSTD' & _ & HER' & _ & QL') & Q8' & HBF' & _) & _).
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    pose proof (tr_un g HGV) as HUN. pose proof (tr_ud g) as HUD.
    apply (ps_open_step (fx := fx') B APIf ra empty FF (HOPEN fx') g 3 [(b, un g); (buf, ubn g)] L A regs' mem' md
      (spk g 48) (wz 0) (wz (uswz g)) lol lvt lvid pad b (uF g) (uC0 g) (Post_o B APIf ra g) FR' HP).
    + rewrite G1. apply ug_ret_ok; lia.
    + rewrite (ss_getr_eqv _ _ 10 XR). reflexivity.
    + rewrite (ss_getr_eqv _ _ 11 XR). reflexivity.
    + unfold spk. lia.
    + unfold spk. lia.
    + unfold spk. lia.
    + exact (rw_cells_transport rsegs [] mem mem' _ _ HPS MU WM I).
    + apply (proj2 (bytes_at_app rsegs mem' G_FILE_LEN _ _)). split; [exact QL'|].
      rewrite length_le8. exact Q8'.
    + exact (proj2 HUN).
    + intros _. left. reflexivity.
    + exact HBF'.
    + exact HSTD'.
    + exact (rw_cells_transport rsegs [] mem mem' _ _ Hofl MU WM I).
    + apply tr_room; [exact HSR | cbn [length]; lia | unfold hb_bytes; cbn [map fold_right snd];
        unfold ubn, ucap; lia | lia].
    + intros L2 A2 regs2 mem2 md2 h2 HGOOD _ RP2 KF2 _ KI2 HSTD2 HG2 HBF2.
      destruct (HGOOD Hgood) as (FR2 & HP2 & R10 & _ & _ & PS2 & MS2 & OO2).
      rewrite (sg_segs B APIf ra empty FF) in KF2, KI2.
      rewrite G1. apply H. exists b, buf, h2. split; [exact Hgood|].
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z) 4 _ _ L2 A2 regs2 mem2 md2 Hfrm FR2 HP2).
      split; [exact R10|].
      split; [|split; [exists pad; exact PS2 | split; [exact MS2 | exact OO2]]].
      apply (tr_TK g b buf regs' regs2 mem' mem2).
      * exact (RP2 8 ltac:(unfold callee_saved; lia)).
      * exact (RP2 9 ltac:(unfold callee_saved; lia)).
      * exact (RP2 26 ltac:(unfold callee_saved; lia)).
      * exact (RP2 27 ltac:(unfold callee_saved; lia)).
      * intros x Hx. apply KF2; unfold spk; lia.
      * intros x Hx. apply KI2; [apply img_w_iff; right; left; unfold G_FILE_LEN in Hx; lia
                                | unfold A_OFL_HEAD, G_FILE_LEN in *; lia].
      * exact HSTD2.
      * exact HG2.
      * exact (tr_errf_o mem' mem2 KI2 HER').
      * exact HBF2.
      * apply (tr_bufc g 4 [(b, un g); (buf, ubn g); (h2, 1304)] L2 A2 regs2 mem2 md2 buf (ubn g) FR2 HP2);
          [right; left; reflexivity | unfold ubn; lia].
      * exact TK'.
Qed.

(* The slot's tail from 0x1306c to the return: close was done; reopen, the call from 24, close, the call on the
   closed reader, free(buf), free(b). *)
Lemma ug_tail : HCT (Inv_K1310c B APIf ra empty) -> Hcut_o B APIf ra (Inv_K130a4 B APIf ra empty) uC0.
Proof. intros H. exact (ug_R1 (ug_R2 (ug_R3 (ug_R4 (ug_R5 (ug_R6 H)))))). Qed.

(* Cut-free twins (SROcf; the cut statements in the PInvCF.Hcut_cf form) of the tail's glue: the same proofs through
   the cut-free steps. Each cut takes the slot's cap bound sb_cap (g_b g) <= CAP_AG and passes it on to the next. *)
Definition HCT_cf (X : ghost -> config -> Prop) : Prop :=
  forall g c, sb_cap (g_b g) <= CAP_AG -> X g c -> SROcf (ms_segs B) c [] (Post_o B APIf ra g).

Hypothesis HFREECF : forall fx0 : FPState, @free_contract_cf fx0 rc B (APIf rc).
Hypothesis LIMLAW : forall L A mem md, aa_MR (APIf rc) L A mem md -> SRC_LIM_MIN <= vm_limit (m_vmmaps md).
Hypothesis HNEXTCF : forall fx0 : FPState, @pcap_source_next_contract_cf fx0.
Hypothesis HCLOSECF : forall fx0 : FPState, pcap_source_close_contract_cf (fx := fx0) B (APIf rc).
Hypothesis HOPENCF : forall fx0 : FPState, pcap_source_open_contract_cf (fx := fx0) B (APIf rc).

Lemma ug_R6_cf : HCT_cf (Inv_K1310c B APIf ra empty) -> HCT_cf (Inv_K13104 B APIf ra empty).
Proof.
  intros H g c Hcap (b & Hgood & HC).
  apply (cut_open_cf B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z) 4 [(b, un g)] _ c [] (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (H8 & Hstd & Hgd & Herr & Hofl).
  pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (_ & _ & _ & _ & HRO).
  apply (run_to_cf B APIf ra empty FF g 4 [(b, un g)] L A regs mem md (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z))
    (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
       (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 8) (getr regs 11) (getr regs 12) (getr regs 13)
       (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
       (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
       (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)) fp_regs (Z_to_bv 64 (symaddr Symbols.Ubsan.s_free)) fp_csr None
       (normalize rsegs mem) (seg_rom rsegs))
    [] (fun c' => SROcf (ms_segs B) c' [] (Post_o B APIf ra g)) (Post_o B APIf ra g) HF HP).
  - rewrite ss_mkR_of. exact (ubs_R6_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr (normalize rsegs mem)).
  - intros ms ->. do 3 eexists. split; [reflexivity|].
    split; [exists []; split; [apply munch_refl|]; split; [apply wmono_refl | intros x _ O; exfalso; exact (O I)]|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ XR HR HF'.
    injection HQ as ER Epc Em. subst R pc' m0'.
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    assert (G10 : getr regs' 10 = wz b) by (rewrite (ss_getr_eqv _ _ 10 XR); exact H8).
    pose proof (tr_rel_mb mem m' HRO HR) as EM.
    rewrite <- (ss_free_pc B APIf ra empty FF).
    apply (ss_free_step_cf B APIf ra empty FF HFREECF g 4 [] b (un g) [] L A regs' m' md [] (Post_o B APIf ra g) HF' HP).
    + rewrite G1. apply ug_ret_ok; lia.
    + exact G10.
    + exact (tr_rel_stdio mem m' HRO HR Hstd).
    + intros L2 A2 regs2 mem2 md2 HF2 HP2 RP2 FRM2 IMG2 STD2 GRD2.
      rewrite G1. apply (H g _ Hcap). exists 4.
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x488)%Z) 4 [] _ L2 A2 regs2 mem2 md2 Hfrm HF2 HP2).
      rewrite (sg_segs B APIf ra empty FF) in IMG2.
      assert (IM : forall x, img_w x -> mbyte rsegs mem2 x = mbyte rsegs mem x)
        by (intros x Hx; rewrite (IMG2 x Hx); apply EM).
      split; [exact STD2|]. split; [exact GRD2|].
      split; [exact (tr_errf mem mem2 IM Herr) | exact (tr_ofl_empty mem mem2 IM Hofl)].
  - intros c' Hc. exact Hc.
Qed.

Lemma ug_R5_cf : HCT_cf (Inv_K13104 B APIf ra empty) -> HCT_cf (Inv_K130f4 B APIf ra empty).
Proof.
  intros H g c Hcap (b & buf & Hgood & HC).
  apply (cut_open_cf B APIf ra empty g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z) 4 [(b, un g); (buf, ubn g)] _ c [] (Post_o B APIf ra g) HC).
  intros fx' L A regs mem md Hfrm HF HP (H10 & ((H8 & H9 & H26 & (Hstd & Hgd & Herr & Q0 & QL) & QG & HBF & Q24) & H27
    & HBUF) & Hofl).
  pose proof (ss_fr_bnd B APIf ra empty FF g _ _ L A regs mem md HF) as (HSP & H16 & HSK & HS47 & HRO).
  assert (USP : bv_unsigned (getr regs 2) = fsp g)
    by (rewrite HSP; unfold fsp, SLOT_FRAME, SS_TOP, SLOT_K, SLOT_STACK in *; apply unsigned_lit; lia).
  assert (Q24n : bytes_at rsegs (normalize rsegs mem) (fsp g + 24) (le8 (wz buf)))
    by (apply bytes_at_normalize; [exact HRO | exact Q24]).
  apply (run_to_cf B APIf ra empty FF g 4 [(b, un g); (buf, ubn g)] L A regs mem md (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z))
    (fun ms' => ms' = MS (mkR (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z)) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
       (getr regs 7) (getr regs 8) (getr regs 9) (wz buf) (wz (-1)) (getr regs 12) (getr regs 13)
       (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19) (getr regs 20)
       (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26) (getr regs 27)
       (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31)) fp_regs (Z_to_bv 64 (symaddr Symbols.Ubsan.s_free)) fp_csr None
       (normalize rsegs mem) (seg_rom rsegs))
    [] (fun c' => SROcf (ms_segs B) c' [] (Post_o B APIf ra g)) (Post_o B APIf ra g) HF HP).
  - rewrite ss_mkR_of. exact (ubs_R5_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5)
      (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
      (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18) (getr regs 19)
      (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25) (getr regs 26)
      (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr (normalize rsegs mem)
      (fsp g) buf USP H10 Q24n).
  - intros ms ->. do 3 eexists. split; [reflexivity|].
    split; [exists []; split; [apply munch_refl|]; split; [apply wmono_refl | intros x _ O; exfalso; exact (O I)]|].
    split; [reflexivity|]. split; reflexivity.
  - intros R pc' m0' regs' m' HQ XR HR HF'.
    injection HQ as ER Epc Em. subst R pc' m0'.
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    assert (G10 : getr regs' 10 = wz buf) by (rewrite (ss_getr_eqv _ _ 10 XR); reflexivity).
    assert (G8 : getr regs' 8 = wz b) by (rewrite (ss_getr_eqv _ _ 8 XR); exact H8).
    pose proof (tr_rel_mb mem m' HRO HR) as EM.
    rewrite <- (ss_free_pc B APIf ra empty FF).
    apply (ss_free_step_cf B APIf ra empty FF HFREECF g 4 [(b, un g)] buf (ubn g) [] L A regs' m' md [] (Post_o B APIf ra g)
      HF' HP).
    + rewrite G1. apply ug_ret_ok; lia.
    + exact G10.
    + exact (tr_rel_stdio mem m' HRO HR Hstd).
    + intros L2 A2 regs2 mem2 md2 HF2 HP2 RP2 FRM2 IMG2 STD2 GRD2.
      rewrite G1. apply (H g _ Hcap). exists b. split; [exact Hgood|].
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x480)%Z) 4 [(b, un g)] _ L2 A2 regs2 mem2 md2 Hfrm HF2 HP2).
      rewrite (sg_segs B APIf ra empty FF) in IMG2.
      assert (IM : forall x, img_w x -> mbyte rsegs mem2 x = mbyte rsegs mem x)
        by (intros x Hx; rewrite (IMG2 x Hx); apply EM).
      split; [transitivity (getr regs' 8); [exact (RP2 8 ltac:(unfold callee_saved; lia)) | exact G8]|].
      split; [exact STD2|]. split; [exact GRD2|].
      split; [exact (tr_errf mem mem2 IM Herr) | exact (tr_ofl_empty mem mem2 IM Hofl)].
  - intros c' Hc. exact Hc.
Qed.

Lemma ug_R4_cf : HCT_cf (Inv_K130f4 B APIf ra empty) -> HCT_cf (Inv_K130e0 B APIf ra empty).
Proof.
  intros H g c Hcap (b & buf & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HTK & Hofl & HPSC).
  destruct HPSC as (lol & lvt & lvid & pad & HPS).
  pose proof HTK as ((_ & E9 & _ & (_ & _ & (fl & mdv & HEF) & _) & _ & _ & Q24) & _ & (bj & HU & HL)).
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (sg_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (tr_fr g _ _ L A regs mem md HF) as (USP & H16 & HFS & ES & HS47).
  destruct (ss_hb_blk B APIf ra empty FF g _ _ L A regs mem md b (un g) HF HP ltac:(left; reflexivity))
    as (_ & Hb4 & _).
  assert (Q24n : bytes_at rsegs (normalize rsegs mem) (fsp g + 24) (le8 (wz buf)))
    by (apply bytes_at_normalize; [exact HMI | exact Q24]).
  apply (ss_kA_run_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z)) mem md
    (fun R pc' m' => R = tregs regs (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z)) (wz (fsp g + 48)) (wz buf) (getr regs 9) (wz 0) /\
       pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next) /\ m' = normalize rsegs mem) _ (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (sg_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_R4_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (fsp g) buf USP Q24n)|].
    intros ms ->. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m' regs' mem' (-> & -> & ->) XR HR HS.
    destruct (tr_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 4 [(b, un g); (buf, ubn g)] L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 4 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); reflexivity | rewrite (ss_getr_eqv _ _ 3 XR); reflexivity
        | rewrite (ss_getr_eqv _ _ 4 XR); reflexivity | exact MU | exact WM | intros lo hi y [] ]. }
    pose proof (tr_TK0 g b buf regs regs' mem mem' MU WM ltac:(rewrite (ss_getr_eqv _ _ 8 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 9 XR); reflexivity) ltac:(rewrite (ss_getr_eqv _ _ 26 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 27 XR); reflexivity) HTK) as TK'.
    pose proof TK' as ((_ & _ & _ & (HSTD' & _) & _ & HBF' & _) & _).
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    apply (ps_next_step_cf (fx := fx') B APIf ra empty FF (HNEXTCF fx') g 4 [(b, un g); (buf, ubn g)] [(b, un g)] L A
      regs' mem' md (spk g 48) buf (ucap g) 0 0 (uswz g) b 24 fl mdv lol lvt lvid (wz 0) (wz 0) (wz 0) pad bj (uF g)
      [] (Post_o B APIf ra g) FR' HP Hfrm).
    + rewrite G1. apply ug_ret_ok; lia.
    + rewrite (ss_getr_eqv _ _ 10 XR). reflexivity.
    + rewrite (ss_getr_eqv _ _ 11 XR). reflexivity.
    + rewrite (ss_getr_eqv _ _ 12 XR). exact E9.
    + rewrite (ss_getr_eqv _ _ 13 XR). reflexivity.
    + unfold spk. lia.
    + unfold spk. lia.
    + unfold spk. lia.
    + exact (rw_cells_transport rsegs [] mem mem' _ _ HPS MU WM I).
    + apply perm_swap.
    + exact (Arr.u8arr_transport rsegs [] mem mem' buf bj HU MU WM I).
    + exact HL.
    + pose proof (tr_ud g). unfold ucap. lia.
    + intros N. exfalso. exact (N eq_refl).
    + intros N. exfalso. exact (N eq_refl).
    + destruct HEF as (E1 & E2). split; [exact (rw_cells_transport rsegs [] mem mem' _ _ E1 MU WM I) | exact E2].
    + intros regs2 mem2 Ft fc' mdv' Hfc _ FR2 RP2 KF2 KH2 KI2 KS2 HE2 HG2 H02 _.
      rewrite (sg_segs B APIf ra empty FF) in KF2, KH2, KI2.
      rewrite G1. apply (H g _ Hcap). exists b, buf. split; [exact Hgood|].
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc') g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x470)%Z) 4 _ _ L A regs2 mem2 md Hfc FR2 HP).
      split; [exact (H02 eq_refl)|].
      split; [|exact (tr_ofl_s mem' mem2 0 KI2 (rw_cells_transport rsegs [] mem mem' _ _ Hofl MU WM I))].
      apply (tr_TK g b buf regs' regs2 mem' mem2).
      * exact (RP2 8 ltac:(unfold callee_saved; lia)).
      * exact (RP2 9 ltac:(unfold callee_saved; lia)).
      * exact (RP2 26 ltac:(unfold callee_saved; lia)).
      * exact (RP2 27 ltac:(unfold callee_saved; lia)).
      * intros x Hx. apply KF2; unfold spk; lia.
      * intros x Hx. apply KI2; [apply img_w_iff; right; left; unfold G_FILE_LEN in Hx; lia
                                | unfold A_STDERR, G_FILE_LEN in *; lia].
      * exact (KS2 HSTD').
      * exact HG2.
      * exists fl, mdv'. exact HE2.
      * apply (tr_mb_bytes mem' mem2 b _); [|exact HBF'].
        intros i Hi. apply (KH2 b (un g) i); [left; reflexivity | lia | unfold un, zlen; lia].
      * apply (tr_bufc g 4 [(b, un g); (buf, ubn g)] L A regs2 mem2 md buf (ubn g) FR2 HP);
          [right; left; reflexivity | unfold ubn; lia].
      * exact TK'.
Qed.

Lemma ug_R3_cf : HCT_cf (Inv_K130e0 B APIf ra empty) -> HCT_cf (Inv_K130d4 B APIf ra empty).
Proof.
  intros H g c Hcap (b & buf & h & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & E10 & HTK & HMS & HOO
    & HPSC).
  destruct HPSC as (lol & lvt & lvid & pad & HPS).
  pose proof HTK as (_ & E27 & _).
  pose proof HF as (_ & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (sg_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (tr_fr g _ _ L A regs mem md HF) as (USP & H16 & HFS & ES & HS47).
  apply (ss_kA_run_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z)) mem md
    (fun R pc' m' => R = tregs regs (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z)) (wz (fsp g + 48)) (getr regs 11) (getr regs 12) (getr regs 13) /\
       pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_close) /\ m' = normalize rsegs mem) _ (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (sg_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_R3_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (fsp g) USP ltac:(rewrite E10, E27; reflexivity))|].
    intros ms ->. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m' regs' mem' (-> & -> & ->) XR HR HS.
    destruct (tr_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 4 [(b, un g); (buf, ubn g); (h, 1304)] L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 4 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); reflexivity | rewrite (ss_getr_eqv _ _ 3 XR); reflexivity
        | rewrite (ss_getr_eqv _ _ 4 XR); reflexivity | exact MU | exact WM | intros lo hi y [] ]. }
    pose proof (tr_TK0 g b buf regs regs' mem mem' MU WM ltac:(rewrite (ss_getr_eqv _ _ 8 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 9 XR); reflexivity) ltac:(rewrite (ss_getr_eqv _ _ 26 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 27 XR); reflexivity) HTK) as TK'.
    pose proof TK' as ((_ & _ & _ & (HSTD' & _ & HER' & _) & _ & _ & _) & _).
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    apply (ps_close_step_cf (fx := fx') B APIf ra empty FF (HCLOSECF fx') g 4 [(b, un g); (buf, ubn g)] h [] L A regs'
      mem' md (spk g 48) (wz (uswz g)) lol lvt lvid pad b (uF g) (upos g (uQ g 24)) [] (Post_o B APIf ra g) FR' HP).
    + rewrite G1. apply ug_ret_ok; lia.
    + rewrite (ss_getr_eqv _ _ 10 XR). reflexivity.
    + unfold spk. lia.
    + unfold spk. lia.
    + unfold spk. lia.
    + exact (rw_cells_transport rsegs [] mem mem' _ _ HPS MU WM I).
    + cbn [app]. left. reflexivity.
    + exact (mstl_transport [] mem mem' h b (uF g) _ _ _ HMS MU WM I I).
    + exact (rw_cells_transport rsegs [] mem mem' _ _ HOO MU WM I).
    + exact HSTD'.
    + intros L2 A2 regs2 mem2 md2 FR2 HP2 RP2 KF2 _ KI2 HPS2 HOE2 HSTD2 HG2 HBF2.
      rewrite (sg_segs B APIf ra empty FF) in KF2, KI2.
      rewrite G1. apply (H g _ Hcap). exists b, buf. split; [exact Hgood|].
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x45c)%Z) 4 _ _ L2 A2 regs2 mem2 md2 Hfrm FR2 HP2).
      split; [|split; [exact HOE2 | exists lol, lvt, lvid, pad; exact HPS2]].
      apply (tr_TK g b buf regs' regs2 mem' mem2).
      * exact (RP2 8 ltac:(unfold callee_saved; lia)).
      * exact (RP2 9 ltac:(unfold callee_saved; lia)).
      * exact (RP2 26 ltac:(unfold callee_saved; lia)).
      * exact (RP2 27 ltac:(unfold callee_saved; lia)).
      * intros x Hx. apply KF2; unfold spk; lia.
      * intros x Hx. apply KI2; [apply img_w_iff; right; left; unfold G_FILE_LEN in Hx; lia
                                | unfold A_OFL_HEAD, G_FILE_LEN in *; lia].
      * exact HSTD2.
      * exact HG2.
      * exact (tr_errf_o mem' mem2 KI2 HER').
      * exact HBF2.
      * apply (tr_bufc g 4 [(b, un g); (buf, ubn g)] L2 A2 regs2 mem2 md2 buf (ubn g) FR2 HP2);
          [right; left; reflexivity | unfold ubn; lia].
      * exact TK'.
Qed.

Lemma ug_R2_cf : HCT_cf (Inv_K130d4 B APIf ra empty) -> Hcut_cf B APIf ra (Inv_K130bc B APIf ra empty) uC0.
Proof.
  intros H g c Hcap (b & buf & h & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & E10 & HTK & HPSC & HMS
    & HOO).
  destruct HPSC as (pad & HPS).
  pose proof HTK as ((_ & E9 & _ & (_ & _ & (fl & mdv & HEF) & _) & _ & _ & Q24) & _ & (bj & HU & HL)).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  unfold MI in HMI. rewrite (sg_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (tr_fr g _ _ L A regs mem md HF) as (USP & H16 & HFS & ES & HS47).
  destruct (ss_hb_blk B APIf ra empty FF g _ _ L A regs mem md h 1304 HF HP
    ltac:(right; right; left; reflexivity)) as (_ & Hh4 & _).
  assert (Hhn : h <> 0) by lia.
  pose proof (tr_neq3 g 4 b (un g) buf (ubn g) h 1304 L A regs mem md HF HP) as Hbh.
  assert (Q24n : bytes_at rsegs (normalize rsegs mem) (fsp g + 24) (le8 (wz buf)))
    by (apply bytes_at_normalize; [exact HMI | exact Q24]).
  rewrite (tr_C0 g h Hhn).
  apply (ss_kA_run_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z)) mem md
    (fun R pc' m' => R = tregs regs (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z)) (wz (fsp g + 48)) (wz buf) (getr regs 9) (wz 0) /\
       pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_next) /\ m' = normalize rsegs mem) _ (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (sg_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_R2_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (fsp g) buf USP E10 Q24n)|].
    intros ms ->. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m' regs' mem' (-> & -> & ->) XR HR HS.
    destruct (tr_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 4 [(b, un g); (buf, ubn g); (h, 1304)] L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 4 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); reflexivity | rewrite (ss_getr_eqv _ _ 3 XR); reflexivity
        | rewrite (ss_getr_eqv _ _ 4 XR); reflexivity | exact MU | exact WM | intros lo hi y [] ]. }
    pose proof (tr_TK0 g b buf regs regs' mem mem' MU WM ltac:(rewrite (ss_getr_eqv _ _ 8 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 9 XR); reflexivity) ltac:(rewrite (ss_getr_eqv _ _ 26 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 27 XR); reflexivity) HTK) as TK'.
    pose proof TK' as ((_ & _ & _ & (HSTD' & _) & _ & HBF' & _) & _).
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    apply (ps_next_step_cf (fx := fx') B APIf ra empty FF (HNEXTCF fx') g 4 [(b, un g); (buf, ubn g); (h, 1304)]
      [(b, un g); (h, 1304)] L A regs' mem' md (spk g 48) buf (ucap g) 0 h (uswz g) b 24 fl mdv (wz 0) (wz 0) (wz 0)
      (wz 0) (wz 0) (wz 0) pad bj (uF g) [] (Post_o B APIf ra g) FR' HP Hfrm).
    + rewrite G1. apply ug_ret_ok; lia.
    + rewrite (ss_getr_eqv _ _ 10 XR). reflexivity.
    + rewrite (ss_getr_eqv _ _ 11 XR). reflexivity.
    + rewrite (ss_getr_eqv _ _ 12 XR). exact E9.
    + rewrite (ss_getr_eqv _ _ 13 XR). reflexivity.
    + unfold spk. lia.
    + unfold spk. lia.
    + unfold spk. lia.
    + exact (rw_cells_transport rsegs [] mem mem' _ _ HPS MU WM I).
    + apply perm_swap.
    + exact (Arr.u8arr_transport rsegs [] mem mem' buf bj HU MU WM I).
    + exact HL.
    + pose proof (tr_ud g). unfold ucap. lia.
    + intros N. exfalso. exact (N eq_refl).
    + intros _. split; [right; left; reflexivity|]. split; [left; reflexivity|].
      split; [exact (mstl_transport [] mem mem' h b (uF g) _ _ _ HMS MU WM I I)|].
      split; [exact (tr_swz g) | exact (proj2 (tr_un g HGV))].
    + destruct HEF as (E1 & E2). split; [exact (rw_cells_transport rsegs [] mem mem' _ _ E1 MU WM I) | exact E2].
    + intros regs2 mem2 Ft fc' mdv' Hfc _ FR2 RP2 KF2 KH2 KI2 KS2 HE2 HG2 _ H12.
      destruct (H12 Hhn) as (R10 & MS2 & PS2 & _).
      rewrite psn_q_UP, res_of_UP in R10. rewrite psn_q_UP, pos_of_UP in MS2.
      rewrite (sg_segs B APIf ra empty FF) in KF2, KH2, KI2.
      rewrite G1. apply (H g _ Hcap). exists b, buf, h. split; [exact Hgood|].
      apply (cut_close B APIf ra empty (YK11.mkFP Ft fc') g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x450)%Z) 4 _ _ L A regs2 mem2 md Hfc FR2 HP).
      split; [exact R10|].
      split; [|split; [exact MS2|]; split;
        [exact (tr_ofl_s mem' mem2 h KI2 (rw_cells_transport rsegs [] mem mem' _ _ HOO MU WM I))
        | do 3 eexists; exists pad; exact PS2]].
      apply (tr_TK g b buf regs' regs2 mem' mem2).
      * exact (RP2 8 ltac:(unfold callee_saved; lia)).
      * exact (RP2 9 ltac:(unfold callee_saved; lia)).
      * exact (RP2 26 ltac:(unfold callee_saved; lia)).
      * exact (RP2 27 ltac:(unfold callee_saved; lia)).
      * intros x Hx. apply KF2; unfold spk; lia.
      * intros x Hx. apply KI2; [apply img_w_iff; right; left; unfold G_FILE_LEN in Hx; lia
                                | unfold A_STDERR, G_FILE_LEN in *; lia].
      * exact (KS2 HSTD').
      * exact HG2.
      * exists fl, mdv'. exact HE2.
      * apply (tr_mb_bytes mem' mem2 b _); [|exact HBF'].
        intros i Hi. apply (KH2 b (un g) i); [left; reflexivity | exact Hbh | unfold un, zlen; lia].
      * apply (tr_bufc g 4 [(b, un g); (buf, ubn g); (h, 1304)] L A regs2 mem2 md buf (ubn g) FR2 HP);
          [right; left; reflexivity | unfold ubn; lia].
      * exact TK'.
Qed.

Lemma ug_R1_cf : Hcut_cf B APIf ra (Inv_K130bc B APIf ra empty) uC0 -> Hcut_cf B APIf ra (Inv_K130a4 B APIf ra empty) uC0.
Proof.
  intros H g c Hcap (b & buf & Hgood & fx' & L & A & regs & mem & md & -> & Hfrm & HF & HP & HTK & Hofl & HPSC).
  destruct HPSC as (lol & lvt & lvid & pad & HPS).
  pose proof HF as (HGV & _ & _ & _ & _ & _ & HMI & _ & HM & _).
  pose proof HGV as (_ & _ & _ & _ & _ & _ & HSR & _).
  unfold MI in HMI. rewrite (sg_segs B APIf ra empty FF) in HMI.
  destruct (mr_model B _ (aa_laws (APIf rc)) _ _ _ _ HM) as (Hh & Hl & _).
  destruct (tr_fr g _ _ L A regs mem md HF) as (USP & H16 & HFS & ES & HS47).
  assert (F0n : bytes_at rsegs (normalize rsegs mem) (fsp g + 48) (le8 (wz 0)))
    by (apply bytes_at_normalize; [exact HMI | exact (tr_f0 _ _ _ _ _ _ _ _ HPS)]).
  apply (ss_kA_run_o_cf B APIf ra empty FF regs (Z_to_bv 64 (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x420)%Z)) mem md
    (fun R pc' m' => R = tregs regs (wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z)) (wz (fsp g + 48)) (wz (symaddr (Symbols.Ubsan.Sec.s_rodata + 0xe9)%Z)) (getr regs 12) (getr regs 13) /\
       pc' = Z_to_bv 64 (symaddr Symbols.Ubsan.s_pcap_source_open) /\ m' = normalize rsegs mem) _ (Post_o B APIf ra g) Hh Hl
    ltac:(rewrite (sg_segs B APIf ra empty FF); exact HMI)).
  - rewrite ss_mkR_of. eapply evt_mono; [exact (ubs_R1_x (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4)
      (getr regs 5) (getr regs 6) (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11)
      (getr regs 12) (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
      (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24) (getr regs 25)
      (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31) fp_regs fp_csr
      (normalize rsegs mem) (fsp g) USP F0n)|].
    intros ms ->. do 3 eexists. split; [reflexivity|]. split; [reflexivity|]. split; reflexivity.
  - intros R pc' m' regs' mem' (-> & -> & ->) XR HR HS.
    destruct (tr_same mem mem' HMI HR HS) as (MU & WM).
    assert (FR' : FR B APIf ra empty g 3 [(b, un g); (buf, ubn g)] L A regs' mem' md).
    { apply (ss_FR_munch B APIf ra empty FF g 3 _ L A regs mem md regs' mem' [] HF HP);
        [rewrite (ss_getr_eqv _ _ 2 XR); reflexivity | rewrite (ss_getr_eqv _ _ 3 XR); reflexivity
        | rewrite (ss_getr_eqv _ _ 4 XR); reflexivity | exact MU | exact WM | intros lo hi y [] ]. }
    pose proof (tr_TK0 g b buf regs regs' mem mem' MU WM ltac:(rewrite (ss_getr_eqv _ _ 8 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 9 XR); reflexivity) ltac:(rewrite (ss_getr_eqv _ _ 26 XR); reflexivity)
      ltac:(rewrite (ss_getr_eqv _ _ 27 XR); reflexivity) HTK) as TK'.
    pose proof TK' as ((_ & _ & _ & (HSTD' & _ & HER' & _ & QL') & Q8' & HBF' & _) & _).
    assert (G1 : getr regs' 1 = wz (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z)) by (rewrite (ss_getr_eqv _ _ 1 XR); reflexivity).
    pose proof (tr_un g HGV) as HUN. pose proof (tr_ud g) as HUD.
    apply (ps_open_step_cf (fx := fx') B APIf ra empty FF (HOPENCF fx') g 3 [(b, un g); (buf, ubn g)] L A regs' mem' md
      (spk g 48) (wz 0) (wz (uswz g)) lol lvt lvid pad b (uF g) (uC0 g) (Post_o B APIf ra g) FR' HP).
    + rewrite G1. apply ug_ret_ok; lia.
    + rewrite (ss_getr_eqv _ _ 10 XR). reflexivity.
    + rewrite (ss_getr_eqv _ _ 11 XR). reflexivity.
    + unfold spk. lia.
    + unfold spk. lia.
    + unfold spk. lia.
    + exact (rw_cells_transport rsegs [] mem mem' _ _ HPS MU WM I).
    + apply (proj2 (bytes_at_app rsegs mem' G_FILE_LEN _ _)). split; [exact QL'|].
      rewrite length_le8. exact Q8'.
    + exact (proj2 HUN).
    + intros _. left. reflexivity.
    + exact HBF'.
    + exact HSTD'.
    + exact (rw_cells_transport rsegs [] mem mem' _ _ Hofl MU WM I).
    + pose proof HSR as (_ & (HB1 & HB2) & (HC1 & HC2)).
      apply room_cf_slot.
      * apply tr_room; [exact HSR | cbn [length]; lia | unfold hb_bytes; cbn [map fold_right snd];
          unfold ubn, ucap; lia | lia].
      * unfold sb_hb; cbn [sb_cap]; lia.
      * unfold sb_hb, hb_bytes; cbn [sb_bytes map fold_right snd]. unfold ubn, ucap. lia.
      * exact (LIMLAW L A mem md HM).
    + intros L2 A2 regs2 mem2 md2 h2 HGOOD _ RP2 KF2 _ KI2 HSTD2 HG2 HBF2.
      destruct (HGOOD Hgood) as (FR2 & HP2 & R10 & _ & _ & PS2 & MS2 & OO2).
      rewrite (sg_segs B APIf ra empty FF) in KF2, KI2.
      rewrite G1. apply (H g _ Hcap). exists b, buf, h2. split; [exact Hgood|].
      apply (cut_close B APIf ra empty fx' g (symaddr (Symbols.Ubsan.s_LLVMFuzzerTestOneInput + 0x438)%Z) 4 _ _ L2 A2 regs2 mem2 md2 Hfrm FR2 HP2).
      split; [exact R10|].
      split; [|split; [exists pad; exact PS2 | split; [exact MS2 | exact OO2]]].
      apply (tr_TK g b buf regs' regs2 mem' mem2).
      * exact (RP2 8 ltac:(unfold callee_saved; lia)).
      * exact (RP2 9 ltac:(unfold callee_saved; lia)).
      * exact (RP2 26 ltac:(unfold callee_saved; lia)).
      * exact (RP2 27 ltac:(unfold callee_saved; lia)).
      * intros x Hx. apply KF2; unfold spk; lia.
      * intros x Hx. apply KI2; [apply img_w_iff; right; left; unfold G_FILE_LEN in Hx; lia
                                | unfold A_OFL_HEAD, G_FILE_LEN in *; lia].
      * exact HSTD2.
      * exact HG2.
      * exact (tr_errf_o mem' mem2 KI2 HER').
      * exact HBF2.
      * apply (tr_bufc g 4 [(b, un g); (buf, ubn g); (h2, 1304)] L2 A2 regs2 mem2 md2 buf (ubn g) FR2 HP2);
          [right; left; reflexivity | unfold ubn; lia].
      * exact TK'.
Qed.

Lemma ug_tail_cf : HCT_cf (Inv_K1310c B APIf ra empty) -> Hcut_cf B APIf ra (Inv_K130a4 B APIf ra empty) uC0.
Proof. intros H. exact (ug_R1_cf (ug_R2_cf (ug_R3_cf (ug_R4_cf (ug_R5_cf (ug_R6_cf H)))))). Qed.

End T.
