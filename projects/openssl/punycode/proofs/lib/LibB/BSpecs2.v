(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk Frame.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import FpLift WpEngine LibKit StrKit WpTac WpMem.
From OSSVerify.Proofs.openssl.punycode.lib.LibA Require Import AShadow.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require Import BCode BRt BImg BRtIc BIface BWpacket BA2u BRtInst.
From OSSVerify.Proofs.openssl.punycode.lib.LibB Require BFakeStack.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma rget_lof : forall regs (k : nat), (0 < k < 32)%nat -> rget (lof regs) k = getr regs (Z_to_bv 5 (Z.of_nat k)).
Proof. intros regs k Hk. symmetry. apply rrel_getr; [apply rrel_lof | exact Hk]. Qed.

Ltac lof_reg :=
  rewrite rget_lof by lia;
  match goal with |- getr _ (Z_to_bv 5 (Z.of_nat ?k)) = _ =>
    let r := eval cbv in (Z.of_nat k) in
    replace (Z_to_bv 5 (Z.of_nat k)) with (Z_to_bv 5 r) by reflexivity end;
  match goal with H : getr _ ?r = ?v |- getr _ ?r' = ?v =>
    replace r' with r by (apply bv_eq; reflexivity); exact H end.

(* [comment removed for export] *)
Lemma seg_rom_above : forall a, B_IMG_END <= a < 2 ^ 64 -> seg_rom BSEGS (W a) = None.
Proof.
  intros a Ha. unfold seg_rom, memory_read. rewrite Wu by (unfold B_IMG_END in Ha; lia).
  change (Z.of_N 1) with 1. rewrite find_segment_above by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma xn_shadow : forall M, cell BSEGS M (sha XNB) 1 (W 5) -> M (W (sha XNB)) = Some (Z_to_bv 8 5).
Proof.
  intros M H. unfold cell in H. cbn [rdn] in H.
  destruct (M (W (sha XNB))) as [b0|] eqn:E.
  - change (word_to_le_bytes 1 (W 5)) with [Z_to_bv 8 5] in H. injection H as ->. reflexivity.
  - rewrite seg_rom_above in H by (split; [unfold B_IMG_END; vm_compute; discriminate | vm_compute; reflexivity]). discriminate H.
Qed.

(* [comment removed for export] *)
Definition dom3_sep (T ctx thr lo n : Z) : Prop :=
  (T + 32 <= lo \/ lo + n <= T + 24) /\ (ctx + 160 <= lo \/ lo + n <= ctx + 152) /\ (thr + 64 <= lo \/ lo + n <= thr + 48).

Lemma apartL : forall u a b lo n lo' n', (a <= lo \/ lo + n <= b) -> lo <= lo' -> lo' + n' <= lo + n ->
  lo' <= u < lo' + n' -> b <= u < a -> False.
Proof. intros. lia. Qed.
Lemma apartR : forall u a b lo n b' a', (a <= lo \/ lo + n <= b) -> b <= b' -> a' <= a ->
  lo <= u < lo + n -> b' <= u < a' -> False.
Proof. intros. lia. Qed.

Lemma FP_not_dom : forall fs T ctx thr L FB6 out b N,
  a2u_sep fs L FB6 out b N -> fs_wf fs -> (B_IMG_END <= FB6 /\ (FB6 + 4096 <= SB \/ HIMEM_BEG <= FB6)) /\ FB6 + 4096 <= HIMEM_END ->
  BFakeStack.fsrt_sep (L - 2400) 2464 fs T ctx thr -> dom3_sep T ctx thr FB6 2400 -> dom3_sep T ctx thr out 16 ->
  dom3_sep T ctx thr fs 1085440 -> dom3_sep T ctx thr SB (HIMEM_BEG - SB) ->
  forall x, a2u_FP fs L FB6 out x -> ~ BFakeStack.fsrt_dom fs T ctx thr x.
Proof.
  intros fs T ctx thr L FB6 out b N (S1 & S2 & S3 & _ & S5 & S6 & S7 & _) ((F0 & F1) & F2 & _) ((A0 & A2) & A3)
    (W1 & W2 & W3 & W4) (D1 & D2 & D3) (O1 & O2 & O3) (R1 & R2 & R3) (Z1 & Z2 & Z3) x Hx Hd.
  assert (Hr : SB <= sha (fs + 36864) /\ sha (fs + 36864) + 131072 <= HIMEM_BEG).
  { clear - F0 F1 F2. unfold B_IMG_END, SB, HIMEM_BEG, HIMEM_END, FS_SIZE in *.
    assert (Hq : (fs + 36864) / 8 <= 17592185913344) by (apply Z.div_le_upper_bound; lia).
    assert (Hq0 : 0 <= (fs + 36864) / 8) by (apply Z.div_pos; lia). unfold sha, SB. lia. }
  assert (Hr6 : SB <= sha FB6 /\ sha FB6 + 512 <= HIMEM_BEG).
  { clear - A0 A2 A3. unfold B_IMG_END, SB, HIMEM_BEG, HIMEM_END in *.
    assert (Hq : FB6 / 8 <= 17592186043904) by (apply Z.div_le_upper_bound; lia).
    assert (Hq0 : 0 <= FB6 / 8) by (apply Z.div_pos; lia). unfold sha, SB. lia. }
  unfold a2u_FP, ring_FP, BFakeStack.fsrt_dom, inr in *.
  set (sf := sha (fs + 36864)) in *. set (s6 := sha FB6) in *. clearbody sf s6.
  set (u := bv_unsigned x) in *. clearbody u. clear x.
  pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' W1) as AW1. pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' W2) as AW2.
  pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' W3) as AW3. pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' W4) as AW4.
  pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' D1) as AD1. pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' D2) as AD2. pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' D3) as AD3.
  pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' O1) as AO1. pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' O2) as AO2. pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' O3) as AO3.
  pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' R1) as AR1. pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' R2) as AR2. pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' R3) as AR3.
  pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' Z1) as AZ1. pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' Z2) as AZ2. pose proof (fun lo' n' => apartL u _ _ _ _ lo' n' Z3) as AZ3.
  pose proof (fun b' a' => apartR u _ _ _ _ b' a' S7) as AS7. pose proof (fun b' a' => apartR u _ _ _ _ b' a' S6) as AS6.
  clear S1 S2 S3 S5 S6 S7 W1 W2 W3 W4 D1 D2 D3 O1 O2 O3 R1 R2 R3 Z1 Z2 Z3.
  unfold B_IMG_END, SB, HIMEM_BEG, HIMEM_END, FS_SIZE in *.
  destruct Hd as [Hd|[Hd|[Hd|Hd]]]; destruct Hx as [H|[H|[H|[H|[H|[H|[H|[H|[H|[H|H]]]]]]]]]];
    first [ lia
          | eapply AW1; [ | | exact H | ]; lia | eapply AW2; [ | | exact H | ]; lia | eapply AW3; [ | | exact H | ]; lia
          | eapply AW4; [ | | exact H | ]; lia
          | eapply AD1; [ | | exact H | ]; lia | eapply AD2; [ | | exact H | ]; lia | eapply AD3; [ | | exact H | ]; lia
          | eapply AO1; [ | | exact H | ]; lia | eapply AO2; [ | | exact H | ]; lia | eapply AO3; [ | | exact H | ]; lia
          | eapply AR1; [ | | exact H | ]; lia | eapply AR2; [ | | exact H | ]; lia | eapply AR3; [ | | exact H | ]; lia
          | eapply AZ1; [ | | exact H | ]; lia | eapply AZ2; [ | | exact H | ]; lia | eapply AZ3; [ | | exact H | ]; lia
          | eapply AS7; [ | | | exact H]; lia | eapply AS6; [ | | | exact H]; lia ].
Qed.

(* [comment removed for export] *)
Theorem a2u_loop_spec : forall regs F fc M rom fs T ctx thr h L FB6 b len N out sb (eb : word),
  getr regs 2%bv = W L -> getr regs 4%bv = W TP -> getr regs 9%bv = W L -> getr regs 18%bv = W SB ->
  getr regs 19%bv = W (sha FB6) -> getr regs 21%bv = W (FB6 + 2208) -> getr regs 25%bv = W FB6 -> getr regs 26%bv = W b ->
  (* [comment removed for export] *)
  0 <= len < 2 ^ 31 -> len < N -> 0 < b -> b + N < 2 ^ 63 -> rd_ok M b N ->
  M (W (b + len)) = Some (Z_to_bv 8 0) -> (b + len) / 8 * 8 + 8 <= b + N ->
  memrange b N -> addr_ok M b (len + 1) -> shw_ok M b (len + 1) ->
  (* [comment removed for export] *)
  cell BSEGS M (FB6 + 2208) 8 (W 0) -> cell BSEGS M (FB6 + 2208 + 8) 8 (W out) -> cell BSEGS M (FB6 + 2208 + 16) 8 (W 0) ->
  cell BSEGS M (FB6 + 2208 + 24) 8 (W 0) -> cell BSEGS M (FB6 + 2208 + 32) 8 (W 16) -> cell BSEGS M (FB6 + 2208 + 40) 8 (W sb) ->
  cell BSEGS M (FB6 + 2208 + 48) 1 eb -> (bv_unsigned eb mod 2 ^ 8) mod 2 = 0 -> 0 < sb < 2 ^ 64 ->
  (* [comment removed for export] *)
  rt_ok M -> ic_ok M -> BFakeStack.fsrt_ok M fs T ctx thr -> BFakeStack.fsrt_wf fs T ctx thr -> uar_on M ->
  cell BSEGS M 0x5e2590 8 (W 0x273608) /\ cell BSEGS M 0x5e2598 8 (W 0x273870) ->
  img_ok M 0xc2ee0 0xc2ee5 -> cell BSEGS M (sha XNB) 1 (W 5) -> shw_ok M XNB 4 ->
  (* [comment removed for export] *)
  fs_wf fs -> 0 <= h < 2 ^ 64 -> cell BSEGS M fs 8 (W h) -> zeros M (fs + 4096) 16384 -> ring_wr M fs ->
  (* [comment removed for export] *)
  FB6 mod 64 = 0 -> B_IMG_END <= FB6 -> (FB6 + 4096 <= SB \/ HIMEM_BEG <= FB6) -> FB6 + 4096 <= HIMEM_END ->
  zeros M (sha FB6 + 276) 7 -> zeros M (sha FB6 + 4) 256 -> rd_ok M (sha FB6) 296 -> wr_ok BSEGS M (sha FB6 + 288) 3 ->
  wr_ok BSEGS M (FB6 + 32) 2048 -> wr_ok BSEGS M (FB6 + 2224) 16 -> wr_ok BSEGS M (FB6 + 2304) 4 -> wr_ok BSEGS M (FB6 + 2320) 6 ->
  (* [comment removed for export] *)
  B_IMG_END <= out -> memrange out 16 -> addr_ok M out 16 -> shw_ok M out 16 -> wr_ok BSEGS M out 16 ->
  (* [comment removed for export] *)
  B_IMG_END <= L - 2400 -> L + 64 < 2 ^ 63 -> L mod 32 = 0 -> wr_ok BSEGS M (L - 2400) 2464 ->
  (* [comment removed for export] *)
  a2u_sep fs L FB6 out b N ->
  BFakeStack.fsrt_sep (L - 2400) 2464 fs T ctx thr -> dom3_sep T ctx thr FB6 2400 -> dom3_sep T ctx thr out 16 ->
  dom3_sep T ctx thr fs 1085440 -> dom3_sep T ctx thr SB (HIMEM_BEG - SB) ->
  exists regs' M' h',
    msteps BSEGS (mkstF regs F fc (W 0x4314f4) M rom) (mkstF regs' F fc (W 0x431800) M' rom)
    /\ (forall r : reg, ~ In (ridx r) KSL -> getr regs' r = getr regs r)
    /\ cell BSEGS M' (L + 24) 8 (getr regs 27%bv) /\ cell BSEGS M' (L + 32) 8 (getr regs 25%bv)
    /\ cell BSEGS M' (L + 40) 8 (getr regs 20%bv)
    /\ 0 <= h' < 2 ^ 64 /\ cell BSEGS M' fs 8 (W h') /\ zeros M' (fs + 4096) 16384
    /\ (forall x, ~ a2u_FP fs L FB6 out x -> M' x = M x) /\ mem_grows M M'.
Proof.
  intros regs F fc M rom fs T ctx thr h L FB6 b len N out sb eb H2 H4 H9 H18 H19 H21 H25 H26
    Hlen HlenN Hb HbN Hrd Hnul Hslack Hbm Hbok Hbsw C0 C8 C16 C24 C32 C40 C48 Heb Hsb
    Hrt Hic Hfsrt Hwf Huar Hgot Hxn Hxs Hxw Hfs Hh Chint Hz Hrwr HF1 HF2 HF2b HF3 Z1 Z2 R6 W6 Wb Wp Wq Ws
    Ho1 Ho2 Ho3 Ho4 Ho5 HL1 HL2 HL3 HwL Hsep Hfsep D1 D2 D3 D4.
  set (B := fun i : Z => match M (W (b + i)) with Some x => x | None => Z_to_bv 8 0 end).
  assert (HB : bytes_at M b N B).
  { intros i Hi. unfold B. destruct (M (W (b + i))) as [x|] eqn:E; [reflexivity|]. exfalso. exact (Hrd i Hi E). }
  assert (HBlen : bv_unsigned (B len) = 0) by (unfold B; rewrite Hnul; reflexivity).
  pose proof (rt_iface_real fs T ctx thr Hwf) as IF.
  pose (Post := fun (pc' : word) (l' : regfile) (M' : mem) =>
     pc' = W 0x431800 /\ same_except KSL (lof regs) l'
     /\ cell BSEGS M' (L + 24) 8 (rget (lof regs) 27) /\ cell BSEGS M' (L + 32) 8 (rget (lof regs) 25)
     /\ cell BSEGS M' (L + 40) 8 (rget (lof regs) 20)
     /\ ring_idle M' fs /\ unch M M' (a2u_FP fs L FB6 out) /\ mem_grows M M').
  assert (HR : reach BSEGS rom (W 0x4314f4) (lof regs) M Post).
  { eapply (a2u_loop_cps _ _ _ fs IF rom Post M L FB6 b len N out sb eb B);
      [ exact HB | split; assumption | split; assumption | exact HBlen | exact Hslack
      | split; [exact Hbm | split; [exact Hbok | exact Hbsw]]
      | unfold pkt_at; repeat split; assumption | exact Hsb | exact Heb | exact Hrt | split; assumption | exact Huar
      | exact Hgot | exact Hxn | split; [apply xn_shadow; exact Hxs | exact Hxw] | exact Hfs
      | split; [exists h; split; assumption | exact Hz] | exact Hrwr | repeat split; assumption
      | repeat split; assumption | repeat split; assumption
      | split; [exact Ho1 | split; [exact Ho2 | split; [exact Ho3 | split; [exact Ho4 | exact Ho5]]]]
      | repeat split; assumption
      | exact HwL | exact Hsep
      | eapply FP_not_dom; [exact Hsep | exact Hfs | split; [split; assumption | assumption] | exact Hfsep | exact D1 | exact D2 | exact D3 | exact D4]
      | eapply BFakeStack.fsrt_sep_sub; [exact Hfsep | lia | lia]
      | reflexivity | lof_reg | lof_reg | lof_reg | lof_reg | lof_reg | lof_reg | lof_reg | lof_reg | ].
    intros l' M' Hl' Hse Cs1 Cs2 Cs3 Hri HU HG. apply reach_done. unfold Post.
    split; [reflexivity|]. split; [exact Hse|]. split; [exact Cs1|]. split; [exact Cs2|]. split; [exact Cs3|].
    split; [exact Hri|]. split; [exact HU | exact HG]. }
  destruct (reach_exF BSEGS rom _ _ F fc _ _ HR) as (pc' & regs' & l' & M' & Hms & HRR & HP).
  destruct HP as (-> & Hse & Cs1 & Cs2 & Cs3 & ((h' & Hh' & Ch') & Hz') & HU & HG).
  rewrite rget_lof in Cs1, Cs2, Cs3 by lia.
  exists regs', M', h'. split; [exact Hms|].
  split; [intros r Hr; eapply same_except_getr; eassumption|].
  split; [exact Cs1|]. split; [exact Cs2|]. split; [exact Cs3|].
  split; [exact Hh'|]. split; [exact Ch'|]. split; [exact Hz'|]. split; [exact HU | exact HG].
Qed.

Print Assumptions a2u_loop_spec.
