(* LLVMFuzzerTestOneInput_kit_strlen_facts: kit row K3 of the image-A walk of LLVMFuzzerTestOneInput
   (LLVMFuzzerTestOneInput_segs.v lc_strlen_facts_stmt), the facts the strlen wrapper's contract
   (TransportRtCg.v astrlen_realizes) asks at op 2's call (+0xa5c) for x = NAME[name mod 3], k = 8, 8 or 5:
   (a) first_byte: the k bytes of the string are not 0 and its NUL is 0, read as the image through K1
       (trans_rom_view_rd; each byte in the string's TRANS_RO_RD range) and st.v lc_rom_bytes (the image bytes of the
       three names and their NUL);
   (b) the rest of the NUL's 8-byte word visible: every byte of [0x10000, 0x616000) has an image byte (AB13.v
       tfib_rom_all), and aview falls back to the image where the memory has no byte;
   (c) aro_unowned: the slot's arodata_okS (lc_base) at the entry, kept by the G journal's image clause (lc_core): an
       in_rom byte lies below 0xa3000, so below the overflow head (lp_ro_below) and outside G_HARNESS
       (inG_G_HARNESS_hull), where the journal's start memory agrees with the entry's. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c YP03.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AsanCells TransportG TransportShape AB13.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TransportRtCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TOps.
Import ListNotations.
Open Scope Z_scope.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.

Section kit. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* The read-only loaded segments of the image lie below 0xa3000 (the proof of AE3h.v tfib_rom_low). *)
Lemma lsf_rom_low : forall a, in_rom segs a -> 0 <= a < 0xa3000.
Proof.
intros a (sg & Hin & Hw & Hr).
assert (H : In (Z.of_N (seg_base sg), Z.of_N (seg_size sg), seg_writable sg)
  (map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs)).
{ exact (in_map (fun s : Segment => (Z.of_N (seg_base s), Z.of_N (seg_size s), seg_writable s)) segs sg Hin). }
remember (Z.of_N (seg_base sg)) as b eqn:Eb. remember (Z.of_N (seg_size sg)) as z eqn:Ez.
remember (seg_writable sg) as wr eqn:Ew. clear Eb Ez Ew.
vm_compute in H.
destruct H as [H|[H|[H|[H|[]]]]]; injection H as <- <- <-; try discriminate; lia.
Qed.

(* A byte the image holds is visible at every memory: aview falls back to the image where the memory has none. *)
Lemma lsf_aview_rom_vis : forall (H : word -> bool) (mem : word -> option byte) a,
  YK11.seg_rom segs (Z_to_bv 64 a) <> None -> aview segs H mem a <> None.
Proof.
intros H mem a Hs. unfold aview, mbyte, mrestrict.
destruct (YK11.seg_rom segs (Z_to_bv 64 a)) as [b|] eqn:E; [|congruence].
destruct (H (Z_to_bv 64 a)); [|destruct (mem (Z_to_bv 64 a))]; cbn [option_map]; discriminate.
Qed.

(* (b): the rest of the 8-byte word after x + k, for a string inside [0x10000, 0x616000 - 8). *)
Lemma lsf_word_vis : forall (W : world segs) (mem : word -> option byte) x k,
  0x10000 <= x -> 0 <= k -> x + k + 8 <= 0x616000 ->
  forall a, x + k < a < x + k - (x + k) mod 8 + 8 -> aview segs (w_H W) mem a <> None.
Proof.
intros W mem x k H1 H2 H3 a Ha. pose proof (Z.mod_pos_bound (x + k) 8 ltac:(lia)) as Hm.
apply lsf_aview_rom_vis. apply AB13.tfib_rom_all. lia.
Qed.

(* A byte of a range of TRANS_RO_RD is a TRANS_RO_RD byte. *)
Lemma lsf_in_ro_rd : forall q n i, In (q, n) TRANS_RO_RD -> 0 <= i < n -> trans_in_ro_rd (q + i).
Proof.
intros q n i Hin Hi. unfold trans_in_ro_rd. apply Exists_exists. exists (q, n).
split; [exact Hin|]. unfold in_zr. cbn [fst snd]. lia.
Qed.

(* (a) for one entry of st.v lc_rom_tab: its first k bytes are not 0 and its byte k is 0, each in TRANS_RO_RD. *)
Lemma lsf_fb : forall (W : world segs) (mem : word -> option byte) q l k,
  trans_rom_view_rd W mem -> In (q, l) lc_rom_tab -> 0 <= k -> length l = S (Z.to_nat k) ->
  (forall i, 0 <= i <= k -> trans_in_ro_rd (q + i)) ->
  (forall i, (i < Z.to_nat k)%nat -> bv_unsigned (nth i l (Z_to_bv 8 0)) <> 0) ->
  bv_unsigned (nth (Z.to_nat k) l (Z_to_bv 8 0)) = 0 ->
  first_byte segs W mem q (k + 1) 0 k.
Proof.
intros W mem q l k HR Hin Hk Hlen Hro Hnz Hz.
assert (RD : forall i, 0 <= i <= k ->
  aview segs (w_H W) mem (q + i) = Some (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0)))).
{ intros i Hi. rewrite (HR (q + i) (Hro i Hi)).
  pose proof (lc_rom_bytes q l Hin (Z.to_nat i) ltac:(lia)) as E.
  rewrite Z2Nat.id in E by lia. exact E. }
unfold first_byte. split; [lia|]. split.
- intros i Hi. exists (bv_unsigned (nth (Z.to_nat i) l (Z_to_bv 8 0))).
  split; [exact (RD i ltac:(lia))|]. apply Hnz. lia.
- intros _. rewrite (RD k ltac:(lia)), Hz. reflexivity.
Qed.

(* (c): aro_unowned at every cut state, from the slot's arodata_okS and the G journal's image clause. *)
Lemma lsf_aro : lp_prem B MT XL RLO RHI -> forall (cx : lcx) ly' S' (W' : world segs) regs' mem' md' e,
  @lc_base rc B MT XL RLO RHI cx -> @lc_core rc B cx ly' S' W' regs' mem' md' e ->
  aro_unowned segs B (aview segs (w_H W') mem').
Proof.
intros HP cx ly' S' W' regs' mem' md' e HB HC.
pose proof (@lp_ro_below _ _ _ _ _ _ HP) as RO.
unfold lc_base, tfib_lib_pre_x in HB.
destruct HB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hrod & _).
destruct HC as (HJ & _).
destruct HJ as (_ & _ & (memS & HJd & Hag) & _).
destruct HJd as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
intros a Hrom Ho He.
pose proof (lsf_rom_low a Hrom) as Hlo.
rewrite (F3 a);
  [| destruct Hrom as (sg & Hin & _ & Hr); exists sg; split; [exact Hin | exact Hr]
   | exact Ho | exact He
   | apply fp_spares_below; exact (@ro_below_ofl_at segs RLO RHI tfib_sink_head RO a (or_introl Hrom))].
assert (Hg : inGb TG.G_HARNESS (bv_unsigned (Z_to_bv 64 a)) = false).
{ rewrite YP03.unsigned_lit_small by lia. apply (proj2 (inGb_false _ _)). intro HG.
  pose proof (inG_G_HARNESS_hull a HG) as Hh. unfold TG.G_HARNESS_LO in Hh. lia. }
assert (E : aview segs (w_H (l_W cx)) memS a = aview segs (w_H (l_W cx)) (l_mem cx) a).
{ unfold aview, mbyte. rewrite (Hag (Z_to_bv 64 a) Hg). reflexivity. }
rewrite E. exact (Hrod a (or_introl Hrom) Ho He).
Qed.

Ltac lsf_in := unfold TRANS_RO_RD, TRANS_RO_GLOBALS; cbn [app]; repeat (first [left; reflexivity | right]).

Lemma lc_strlen_facts_ok (K1 : lc_rom_view_stmt B MT XL RLO RHI) : lc_strlen_facts_stmt B MT XL RLO RHI.
Proof.
unfold lc_strlen_facts_stmt.
intros HP cx ly' S' W' regs' mem' md' e nm HB HC.
pose proof (K1 HP cx ly' S' W' regs' mem' md' e HB HC) as HR.
pose proof (lsf_aro HP cx ly' S' W' regs' mem' md' e HB HC) as HU.
cbv zeta. unfold lc_name_a.
assert (Hm : nm mod 3 = 0 \/ nm mod 3 = 1 \/ nm mod 3 = 2)
  by (pose proof (Z.mod_pos_bound nm 3 ltac:(lia)); lia).
destruct Hm as [Hm | [Hm | Hm]]; rewrite Hm.
- change (nth (Z.to_nat 0) [TRANS_STR_C24; TRANS_STR_PC; TRANS_STR4] 0) with TRANS_STR_C24.
  change (Z.of_nat (length (nth (Z.to_nat 0) TOP.op_announce_NAME []))) with 8.
  split; [|split; [|exact HU]].
  + apply (lsf_fb W' mem' TRANS_STR_C24 (nth 0 TOP.op_announce_NAME [] ++ [DSpec.b8 0]) 8 HR).
    * unfold lc_rom_tab. do 12 right. left. reflexivity.
    * lia.
    * reflexivity.
    * intros i Hi. apply (lsf_in_ro_rd TRANS_STR_C24 9 i); [lsf_in | lia].
    * intros i Hi. do 8 (destruct i as [|i]; [intro E; vm_compute in E; discriminate E|]). lia.
    * vm_compute. reflexivity.
  + exact (lsf_word_vis W' mem' TRANS_STR_C24 8 ltac:(unfold TRANS_STR_C24; lia) ltac:(lia)
      ltac:(unfold TRANS_STR_C24; lia)).
- change (nth (Z.to_nat 1) [TRANS_STR_C24; TRANS_STR_PC; TRANS_STR4] 0) with TRANS_STR_PC.
  change (Z.of_nat (length (nth (Z.to_nat 1) TOP.op_announce_NAME []))) with 8.
  split; [|split; [|exact HU]].
  + apply (lsf_fb W' mem' TRANS_STR_PC (nth 1 TOP.op_announce_NAME [] ++ [DSpec.b8 0]) 8 HR).
    * unfold lc_rom_tab. do 13 right. left. reflexivity.
    * lia.
    * reflexivity.
    * intros i Hi. apply (lsf_in_ro_rd TRANS_STR_PC 9 i); [lsf_in | lia].
    * intros i Hi. do 8 (destruct i as [|i]; [intro E; vm_compute in E; discriminate E|]). lia.
    * vm_compute. reflexivity.
  + exact (lsf_word_vis W' mem' TRANS_STR_PC 8 ltac:(unfold TRANS_STR_PC; lia) ltac:(lia)
      ltac:(unfold TRANS_STR_PC; lia)).
- change (nth (Z.to_nat 2) [TRANS_STR_C24; TRANS_STR_PC; TRANS_STR4] 0) with TRANS_STR4.
  change (Z.of_nat (length (nth (Z.to_nat 2) TOP.op_announce_NAME []))) with 5.
  split; [|split; [|exact HU]].
  + apply (lsf_fb W' mem' TRANS_STR4 (nth 2 TOP.op_announce_NAME [] ++ [DSpec.b8 0]) 5 HR).
    * unfold lc_rom_tab. do 14 right. left. reflexivity.
    * lia.
    * reflexivity.
    * intros i Hi. apply (lsf_in_ro_rd TRANS_STR4 6 i); [lsf_in | lia].
    * intros i Hi. do 5 (destruct i as [|i]; [intro E; vm_compute in E; discriminate E|]). lia.
    * vm_compute. reflexivity.
  + exact (lsf_word_vis W' mem' TRANS_STR4 5 ltac:(unfold TRANS_STR4; lia) ltac:(lia)
      ltac:(unfold TRANS_STR4; lia)).
Qed.

End kit.

Print Assumptions lc_strlen_facts_ok.
