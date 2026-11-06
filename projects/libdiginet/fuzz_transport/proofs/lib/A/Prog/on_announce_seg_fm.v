(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YCbq.v:528-543, 616-634;
   projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC05.v:41-45, 208-214, 230-234, for libreac/fuzz_identity's asan-ubsan build
   (lib/B). The same text also appears in projects/cgif/cgif_file_fuzzer/proofs/lib/YCbo.v:420-423, 430-444, 447-448,
   453-455, 470-475, 477-486, 489-491, 502-505, 511-514, 1255-1258. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/reac_box_name_seg_rel.v, with its module paths, module names and numbers changed; 706 of its 765 lines of code are new or changed and 1865 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/on_announce_seg_tail.v, with its module names changed; 895 of its 985 lines of code are new or changed and 675 lines of the source are left out. *)
(* on_announce_seg_fm: Theorem onann_piece_fm : onann_fm_stmt (lib/A/Prog/OnannCut.v), the find_mac piece of the walk
   of on_announce on fuzz_transport.asan (0x87a74 = transport_sigma TS_on_announce), code +0x2a8 .. +0x304
   (0x87d1c .. 0x87d78), find_mac (transport/src/diginet_session.c:168-174) inlined; from the cut onann_fm_at to the
   desk notice cut onann_dn_at (+0x308).
   What the code does (s1 = sp1, s2 = the frame F, s4 = s = g_s, a = F + 256):
     +0x2a8 .. +0x2c4  fp kept at sp1 + 48; a0 = a (from sp1 + 56); s6 = unknown_len = 15 (the 8 bytes at a + 32),
                       s10 = 6; `bltu s6, s10` not taken; the shadow base kept at sp1 + 24; s7 = unknown = buf + 30
                       (the 8 bytes at a + 24); s8 = i = 0;
     +0x2c8 .. +0x2d8  the loop head: a0 = s7 + s10 - 6 = buf + 30 + i, a2 = 6, a1 = s; the call of the bcmp
                       wrapper (return address +0x2dc);
     +0x2dc            `beqz a0`: when the 6 bytes agree, +0x2fc .. +0x304: a3 = i, s8 and s6 reloaded from sp1 + 24
                       and sp1 + 48, on to +0x308;
     +0x2e0 .. +0x2e8  s10 + 1, s8 + 1 (addiw), `bgeu s6, s10` back to +0x2c8 while i + 7 <= 15; after i = 9,
                       +0x2ec .. +0x2f8: s8 and s6 reloaded, a3 = -1, `j` to +0x308.
   The proof. Run 1 (TransportGRunA.v paj_run_to_x) from the cut to the loop head. The loop invariant fm_inv at
   +0x2c8 (s4 = s, s6 = 15, s7 = buf + 30, s8 = i, s10 = i + 6, the two spill slots sp1 + 24 and sp1 + 48, every
   byte outside fm_Z, the bcmp window [sp1 - 2 * ESTACK, sp1) and the two slots, as at the cut), proved for i = 0 .. 9
   by induction on the turns left (fm_loop). One turn (fm_turn): a run from fm_entryL to the call; the bcmp wrapper by
   its contract abcmp_realizes read at the caller's G journal (fm_bcmp, a copy of check_latest_sent_seg_cj.v cls_bcmp
   through TransportGCg.v gx_call_leaf): a0 = 0 exactly when the 6 bytes at buf + 30 + i and at s agree, which is
   TSess0.v memeq 6 (skipn i (ann_unknown body)) (S_cfg_host_mac W1) (fm_memeq_iff, with the body bytes kept from the
   entry by on_announce_seg_kit.v onann_src_kept and host_mac read through the world relation at W1); the branches
   are taken up again from a fresh symbolic state at +0x2dc. Both exits reach +0x308 with a3 = TSess.v find_mac_m
   (ann_unknown body) 15 (S_cfg_host_mac W1) = onann_off W1 b and conclude by onann_dn_at (fm_exit); the cut's facts
   move to the exit memory by fm_cur_move (what the call keeps: TransportGFrame.v dk_kept_step_gw, every byte changed
   lying in fm_Z, inside the call's stack window). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportSyms DgnTransportList DgnTransportAddr DgnTransportPa DgnTransportImg DgnTransportPaLib YC4b YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG AF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import
DgnTransportCg TransportGCg TransportGRwA TransportGRunA CanKit TransportGFrame.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_ack_cg on_announce_cg OnannCut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import on_announce_seg_kit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TImg TSess0 TSess TCb TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T Require on_announce_lem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TS0 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess0.
Module TSS := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TSess.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module OAL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Prog.T.on_announce_lem.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* 1. The code points and the symbolic states                          *)
(* ------------------------------------------------------------------ *)

(* The loop head (+0x2c8) and the return address of the bcmp call (+0x2dc). *)
Definition FM_LP : Z := AF_on_announce + 0x2c8.
Definition FM_RA : Z := AF_on_announce + 0x2dc.
Lemma fm_pcs : ONANN_FM = 27320 /\ FM_LP = 27352 /\ FM_RA = 27372 /\ ONANN_DN = 27416.
Proof. repeat split; reflexivity. Qed.

(* Run 1 from the cut: the two slots it writes (sp1 + 24, sp1 + 48), the slot it reads (sp1 + 56 = a) and the two
   words of a it reads (unknown = buf + 30, atom 32, at a + 24; unknown_len = 15 at a + 32). *)
Definition FM_R24 : YP09.region := YP09.mkRegion (Some 9%nat) 24 32 24 32 [].
Definition FM_R48 : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition FM_R56 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 56 64 0 0 [YP09.mkChunk 56 (YP09.CVal 8 (SOff 18 256))].
Definition FM_RAa : YP09.region :=
  YP09.mkRegion (Some 18%nat) 280 296 0 0
    [YP09.mkChunk 280 (YP09.CVal 8 (SOff 32 0)); YP09.mkChunk 288 (YP09.CVal 8 (SLit 15))].
(* s1 = sp1 (atom 9) lies in [2 ^ 46, 2 ^ 47] and is 32-aligned: the writable slots are off the shadow token span. *)
Definition ss_fm : sstate :=
  mkSS ONANN_FM sr_atoms [FM_R24; FM_R48; FM_R56; FM_RAa] None (mkFacts [(9%nat, mkAF (2 ^ 46) (2 ^ 47) 5)] [] []).

(* The loop's states (+0x2c8 and +0x2dc): the two slots, read (the shadow base at sp1 + 24, fp = atom 32 at
   sp1 + 48); s6 = 15, s8 = i in [0, 9], s10 = i + 6 in [6, 15]. *)
Definition FM_L24 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 24 32 0 0 [YP09.mkChunk 24 (YP09.CVal 8 (SLit SHADOW_OFF))].
Definition FM_L48 : YP09.region :=
  YP09.mkRegion (Some 9%nat) 48 56 0 0 [YP09.mkChunk 48 (YP09.CVal 8 (SOff 32 0))].
Definition FM_FACTS : facts :=
  mkFacts [(22%nat, mkAF 15 15 0); (24%nat, mkAF 0 9 0); (26%nat, mkAF 6 15 0)] [] [].
Definition fm_ss (pc : Z) : sstate := mkSS pc sr_atoms [FM_L24; FM_L48] None FM_FACTS.
Definition FM_Bx : sv := SLit 0.
Definition FM_B0 : Z * Z := (0, 0).

(* ------------------------------------------------------------------ *)
(* 2. Generic facts                                                    *)
(* ------------------------------------------------------------------ *)

Lemma fm_nth_skipn : forall {A : Type} k (l : list A) i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  intros A k. induction k as [|k IH]; intros l i d; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct i; reflexivity | apply IH].
Qed.

Lemma fm_nth_firstn : forall {A : Type} n (l : list A) i d, (i < n)%nat -> nth i (firstn n l) d = nth i l d.
Proof.
  intros A n. induction n as [|n IH]; intros l i d Hi; [lia|].
  destruct l as [|x l]; [destruct i; reflexivity|]. destruct i as [|i]; [reflexivity|].
  cbn. apply IH. lia.
Qed.

(* find_mac's turn i compares the 6 bytes of the body from i with host_mac: memeq is the bytes' equality. *)
Lemma fm_memeq_iff : forall (u mac : list byte) (i : Z) (rd : Z -> option Z) (x y : Z),
  0 <= i -> i + 6 <= 15 ->
  (forall j, 0 <= j < 15 -> rd (x + j) = Some (DSpec.at8 u (Z.to_nat j))) ->
  (forall j, 0 <= j < 6 -> rd (y + j) = Some (DSpec.at8 mac (Z.to_nat j))) ->
  (TS0.memeq 6 (skipn (Z.to_nat i) u) mac = true <-> (forall j, 0 <= j < 6 -> rd (x + i + j) = rd (y + j))).
Proof.
  intros u mac i rd x y Hi0 Hi6 Hu Hm. unfold TS0.memeq. rewrite forallb_forall. split.
  - intros H j Hj.
    assert (Hin : In (Z.to_nat j) (seq 0 6)) by (apply in_seq; lia).
    specialize (H _ Hin). cbv beta in H. apply Z.eqb_eq in H.
    replace (x + i + j) with (x + (i + j)) by lia.
    rewrite (Hu (i + j) ltac:(lia)), (Hm j Hj). f_equal.
    unfold DSpec.at8 in *. rewrite fm_nth_skipn in H.
    replace (Z.to_nat (i + j)) with (Z.to_nat i + Z.to_nat j)%nat by lia. exact H.
  - intros H j0 Hj0. apply in_seq in Hj0. cbv beta. apply Z.eqb_eq.
    specialize (H (Z.of_nat j0) ltac:(lia)).
    replace (x + i + Z.of_nat j0) with (x + (i + Z.of_nat j0)) in H by lia.
    rewrite (Hu (i + Z.of_nat j0) ltac:(lia)), (Hm (Z.of_nat j0) ltac:(lia)) in H.
    injection H as H. rewrite Nat2Z.id in H.
    unfold DSpec.at8 in *. rewrite fm_nth_skipn.
    replace (Z.to_nat (i + Z.of_nat j0)) with (Z.to_nat i + j0)%nat in H by lia. exact H.
Qed.

(* find_mac_loop's turn. *)
Lemma fm_find_S : forall u mac i f,
  TSS.find_mac_loop u mac i (S f) = if TS0.memeq 6 (skipn (Z.to_nat i) u) mac then i
                                    else TSS.find_mac_loop u mac (i + 1) f.
Proof. reflexivity. Qed.

(* The body bytes find_mac reads are b's from 30 on. *)
Lemma fm_u_at : forall (b : list byte) (j : nat), (j < 15)%nat -> 33 <= DSpec.fr_body_len b ->
  DSpec.at8 (DSpec.ann_unknown (DSpec.fr_body b)) j = bv_unsigned (nth (30 + j) b (Z_to_bv 8 0)).
Proof.
  intros b j Hj H33. unfold DSpec.at8, DSpec.ann_unknown, DSpec.fr_body, DSpec.bz, DSpec.b8.
  rewrite fm_nth_firstn by lia. rewrite fm_nth_firstn by lia. rewrite fm_nth_skipn. reflexivity.
Qed.

(* host_mac is the 6 bytes of g_s's payload at 0 (TWorld.v A_S_cfg_host_mac, at its numeral offset). *)
Lemma fm_mac_eq : forall X, TW.S_cfg_host_mac X = TW.sub X 1648 6.
Proof. intros X. reflexivity. Qed.

(* An announce field holds at most 10 bytes. *)
Lemma fm_field_len : forall src, (length (TSS.ann_field src) <= 10)%nat.
Proof.
  intros src. unfold TSS.ann_field, DSpec.copy_len. rewrite length_app, length_firstn. cbn [length].
  pose proof (DSpec.nz_run_le (firstn (Nat.min 9 (10 - 1)) src)) as H. rewrite length_firstn in H. lia.
Qed.

(* `add a0, s7, s10` then `addi a0, a0, -6`. *)
Lemma fm_a0 : forall E x y, ew E 23 = w64 x -> ew E 26 = w64 y -> 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  sv_denot E (SAlu ALU_ADD (SOff 23 (-6)) (SOff 26 0)) = w64 (x - 6 + y).
Proof.
  intros E x y Hx Hy Rx Ry. cbn [sv_denot]. rewrite Hx, Hy. unfold w64.
  rewrite !unsigned_lit_small by lia. rewrite zalu64_sound. apply Z_to_bv64_eq_mod.
  unfold zalu64, zcanon, M64. cbn [zalu_raw]. rewrite Z.mod_mod by lia. rewrite <- Z.add_mod by lia.
  f_equal. lia.
Qed.

Lemma fm_eqz : forall v : word, bv_eqb v (Z_to_bv 64 0) = true -> v = Z_to_bv 64 0.
Proof. intros v H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Lemma fm_mod16 : forall a c, a mod 32 = 0 -> c mod 16 = 0 -> (a - c) mod 16 = 0.
Proof. intros a c Ha Hc. Z.div_mod_to_equations. lia. Qed.

(* A word read through the view, moved to a memory with the same view at its 8 bytes. *)
Lemma fm_rdmove : forall (rd rd' : Z -> option Z) a v, (forall k, 0 <= k < 8 -> rd' (a + k) = rd (a + k)) ->
  rdword rd a = Some v -> rdword rd' a = Some v.
Proof. intros rd rd' a v Hk H. rewrite (rdword_ext rd rd' a Hk). exact H. Qed.

(* garr8, moved to a memory with the same view at its bytes. *)
Lemma fm_garr8_move : forall (H : word -> bool) (m m' : word -> option byte) p (l : list Z),
  garr8 tfibsegs (mrestrict H m) p l ->
  (forall j, (j < length l)%nat -> aview tfibsegs H m' (p + Z.of_nat j) = aview tfibsegs H m (p + Z.of_nat j)) ->
  garr8 tfibsegs (mrestrict H m') p l.
Proof.
  intros H m m' p l G K j Hj. destruct (G j Hj) as [V R]. split; [|exact R].
  intros k0 Hk0. specialize (V k0 Hk0). assert (k0 = 0%nat) by lia. subst k0.
  replace (p + Z.of_nat j + Z.of_nat 0) with (p + Z.of_nat j) in * by lia.
  rewrite (mbyte_of_aview tfibsegs H H m m' (p + Z.of_nat j) (K j Hj)). exact V.
Qed.

(* A chunk of w bytes of the value e reads, byte k, the k-th little-endian byte of e. *)
Lemma fm_chunk_val : forall E (H : word -> bool) (m : word -> option byte) bopt lo hi wlo whi cs off (w : N) e,
  region_ok tfibsegs E (mrestrict H m) (YP09.mkRegion bopt lo hi wlo whi cs) ->
  In (YP09.mkChunk off (YP09.CVal w e)) cs -> (Z.of_N w <= 8) ->
  val_mem tfibsegs (mrestrict H m) (base_val E bopt + off) (N.to_nat w)
    (bv_unsigned (sv_denot E e) mod 2 ^ (8 * Z.of_N w)).
Proof.
  intros E H m bopt lo hi wlo whi cs off w e (_ & _ & _ & Hcs) Hin Hw.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hc. cbn [YP09.r_base] in Hc.
  exact (val_of_chunk_any tfibsegs E _ _ off w e Hc Hw).
Qed.

(* The value of register r in the machine state of a symbolic state HS: its symbolic value, computed, then tac. *)
Ltac fm_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok ?segsx ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_restrict_reg segsx Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  | ?T => idtac "fm_reg: no match for" T; fail
  end.

(* A register whose symbolic value is its own atom n, from the equation Q of its value at the state's start. *)
Ltac fm_kreg HS EE r n Q H :=
  lazymatch type of Q with _ = ?v =>
    fm_reg HS r v H ltac:(cbn [sv_denot]; rewrite (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact Q) end.
(* The same, the value read off the register map R0 the state's valuation was made from. *)
Ltac fm_kreg0 HS EE R0 r n H :=
  fm_reg HS r (YK11.getr R0 r) H
    ltac:(cbn [sv_denot]; rewrite (EE n r eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).

(* The windows a run wrote, computed, each closed by tac. *)
Ltac fm_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* The write right of a run from a state whose regions are all read-only. *)
Ltac fm_awr0 :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
    [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
      cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |]);
  apply awr_ok_x_nil.

(* ------------------------------------------------------------------ *)
(* 3. The bcmp wrapper at the G journal                                *)
(* ------------------------------------------------------------------ *)

Section fb. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Variable B : asyms.
Hypothesis LAWS : AR_laws tfibsegs B.
Local Abbreviation ajournal_gx := (@W_journalG.ajournal_gx rc tfib_sink_head tfibsegs B).

(* check_latest_sent_seg_cj.v cls_bcmp: the bcmp wrapper's contract (YG0d.v abcmp_realizes), read at the walk's G
   journal through YCbq.v aj_bcmp_at and TransportGCg.v gx_call_leaf. *)
Lemma fm_bcmp :
  forall (STK sp0 : Z) FP ly S (W0 : world tfibsegs) mem0 md0 own lyc Sc (W : world tfibsegs)
         (memT : word -> option byte) mdc k (regsT : bvmap 5 word) (x y n o : Z) (raw : word),
  @abcmp_realizes fx rc tfibsegs B (transport_sigma TS___interceptor_trampoline_bcmp) ->
  ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k ->
  YK11.getr regsT 10 = w64 x -> YK11.getr regsT 11 = w64 y -> YK11.getr regsT 12 = w64 n ->
  0 <= n < 2 ^ 32 -> 0 <= x -> x + n <= 2 ^ 63 -> 0 <= y -> y + n <= 2 ^ 63 ->
  spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> 2 * ESTACK - o <= STK ->
  YK11.getr regsT 3 = w64 (as_gp B) -> YK11.getr regsT 4 = w64 (as_tp B) ->
  YK11.getr regsT 1 = raw -> YK0s.ret_ok raw ->
  src_ok tfibsegs W regsT memT x n -> src_ok tfibsegs W regsT memT y n ->
  (forall a, x <= a < x + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  (forall a, y <= a < y + n -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o)) ->
  amem_range x n -> amem_range y n ->
  range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF x n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) x n) ->
  range_addressable (aview tfibsegs (w_H W) memT) SHADOW_OFF y n ->
  (0 < n -> shadow_hull_vis (aview tfibsegs (w_H W) memT) y n) ->
  SRr tfibsegs W
    (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) memT
              (YK11.seg_rom tfibsegs)) mdc)
    (fun W2 c2 => W2 = W /\ exists regs2 mem2 md2,
       c2 = mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom tfibsegs)) md2 /\
       ajournal_gx TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem2 md2 k /\
       (exists v : word, aregs_preserved regsT regs2 /\ YK11.getr regs2 10 = v /\
          (v = w64 0 <-> forall i, 0 <= i < n ->
             aview tfibsegs (w_H W) memT (x + i) = aview tfibsegs (w_H W) memT (y + i)) /\
          (forall a, 0 <= a < 2 ^ 64 -> ~ (sp0 + o - 2 * ESTACK <= a < sp0 + o) ->
             aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) memT a) /\
          (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a))).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memT mdc k regsT x y n o raw
    AM HJ H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
    Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy.
  apply (@gx_call_leaf fx rc tfib_sink_head tfibsegs B TG.G_HARNESS STK sp0 FP ly S W0 mem0 md0 own
           lyc Sc W memT mdc k _ raw _ HJ).
  intros memS HJi.
  eapply SRr_mono.
  { exact (@aj_bcmp_at fx rc tfib_sink_head tfibsegs B LAWS transport_segs_low
             (transport_sigma TS___interceptor_trampoline_bcmp) AM W regsT memT STK sp0 FP ly S W0 memS md0 own
             lyc Sc mdc k x y n o raw HJi H10 H11 H12 Hn Hx0 Hxn Hy0 Hyn Hsp Hal Hneg Hbud Hgp Htp Hra Hraw
             Hsx Hsy Hbx Hby Hmx Hmy Hrx Hhx Hry Hhy). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & Hc & HJ2 & HP & Hres & Hcmp & Hfr2 & Hpres2).
  split; [reflexivity|]. exists regs2, mem2, md2. split; [exact Hc|]. split; [exact HJ2|].
  exists v. split; [exact HP|]. split; [exact Hres|]. split; [exact Hcmp|]. split; [exact Hfr2 | exact Hpres2].
Qed.

End fb.

(* ------------------------------------------------------------------ *)
(* 4. The symbolic states, from the machine facts                      *)
(* ------------------------------------------------------------------ *)

Section fe. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of run 1: the registers at the cut, then unknown = buf + 30 (atom 32). *)
Definition fm_E0 (R : bvmap 5 word) (buf : Z) : env := Eimg (PI := PI_transport) (Ereg R [w64 (buf + 30)]).
(* The valuation of the loop's states: the registers, then fp (atom 32). *)
Definition fm_EL (R : bvmap 5 word) (fp : Z) : env := Eimg (PI := PI_transport) (Ereg R [w64 fp]).

Lemma fm_entry0 : forall (W : world segs) R mem sp1 F buf,
  YK11.getr R 9 = w64 sp1 -> YK11.getr R 18 = w64 F ->
  4096 <= F -> F + 1024 <= sp1 -> 2 ^ 46 <= sp1 <= 2 ^ 47 -> sp1 mod 32 = 0 -> 0 <= buf + 30 < 2 ^ 64 ->
  (forall a, sp1 + 24 <= a < sp1 + 32 -> apresent (w_H W) mem a) ->
  (forall a, sp1 + 48 <= a < sp1 + 56 -> apresent (w_H W) mem a) ->
  rdword (aview segs (w_H W) mem) (sp1 + 56) = Some (F + ONANN_A) ->
  rdword (aview segs (w_H W) mem) (F + ONANN_A + 24) = Some (buf + 30) ->
  rdword (aview segs (w_H W) mem) (F + ONANN_A + 32) = Some 15 ->
  st_ok_pi segs VAL (fm_E0 R buf) ss_fm
    (restrict (w_H W) (@YK11.mkst fx R (Z_to_bv 64 (BASE + ONANN_FM)) mem (YK11.seg_rom segs))).
Proof.
  intros W R mem sp1 F buf R9 R18 HF0 HFs Hsp Hsp32 Hbuf P24 P48 S56 A24 A32.
  set (E := fm_E0 R buf).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr R r)
    by (intros n r Hn; unfold E, fm_E0; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U18 : bv_unsigned (ew E 18) = F)
    by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = w64 (buf + 30))
    by (unfold E, fm_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra R _ 0)).
  rewrite restrict_mkst_fx. unfold ss_fm.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks FM_R24 FM_R48 FM_R56 FM_RAa base_val];
      rewrite ?U9, ?U18.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply P24. lia.
    + split; [lia|]. split; [lia|]. split; [|constructor].
      intros o Ho. apply (apresent_writable segs). apply P48. lia.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 56 8 (SOff 18 256) (F + ONANN_A));
        [cbn [sv_denot]; rewrite U18; reflexivity
        | unfold ONANN_A; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword segs (w_H W) mem _ _ S56).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      * apply (chunk_ok_val segs E _ F 280 8 (SOff 32 0) (buf + 30));
          [cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small, Z.add_0_r by lia; reflexivity
          | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
        replace (F + 280) with (F + ONANN_A + 24) by (unfold ONANN_A; lia).
        exact (val_mem_of_rdword segs (w_H W) mem _ _ A24).
      * apply (chunk_ok_val segs E _ F 288 8 (SLit 15) 15); [reflexivity | lia | lia |].
        replace (F + 288) with (F + ONANN_A + 32) by (unfold ONANN_A; lia).
        exact (val_mem_of_rdword segs (w_H W) mem _ _ A32).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, FM_R24, FM_R48, FM_R56, FM_RAa.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U18.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U9. change (2 ^ 5) with 32.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

Lemma fm_entryL : forall (W : world segs) R mem pc sp1 fp i,
  YK11.getr R 9 = w64 sp1 -> YK11.getr R 22 = w64 15 -> YK11.getr R 24 = w64 i -> YK11.getr R 26 = w64 (i + 6) ->
  0 <= i <= 9 -> 0 <= sp1 -> sp1 + 64 <= 2 ^ 64 -> 0 <= fp < 2 ^ 64 ->
  rdword (aview segs (w_H W) mem) (sp1 + 24) = Some SHADOW_OFF ->
  rdword (aview segs (w_H W) mem) (sp1 + 48) = Some fp ->
  st_ok_pi segs VAL (fm_EL R fp) (fm_ss pc)
    (restrict (w_H W) (@YK11.mkst fx R (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
  intros W R mem pc sp1 fp i R9 R22 R24 R26 Hi Hsp0 Hsp Hfp S24 S48.
  set (E := fm_EL R fp).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr R r)
    by (intros n r Hn; unfold E, fm_EL; apply ew_Eimg_Ereg_nat; exact Hn).
  assert (U9 : bv_unsigned (ew E 9) = sp1)
    by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
  assert (U22 : bv_unsigned (ew E 22) = 15)
    by (rewrite (EE 22%nat 22%bv eq_refl), R22; unfold w64; apply unsigned_lit_small; lia).
  assert (U24 : bv_unsigned (ew E 24) = i)
    by (rewrite (EE 24%nat 24%bv eq_refl), R24; unfold w64; apply unsigned_lit_small; lia).
  assert (U26 : bv_unsigned (ew E 26) = i + 6)
    by (rewrite (EE 26%nat 26%bv eq_refl), R26; unfold w64; apply unsigned_lit_small; lia).
  assert (E32 : ew E 32 = w64 fp)
    by (unfold E, fm_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra R _ 0)).
  rewrite restrict_mkst_fx. unfold fm_ss.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks FM_L24 FM_L48 base_val];
      rewrite ?U9.
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 24 8 (SLit SHADOW_OFF) SHADOW_OFF);
        [reflexivity | unfold SHADOW_OFF; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword segs (w_H W) mem _ _ S24).
    + split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_nil].
      apply (chunk_ok_val segs E _ sp1 48 8 (SOff 32 0) fp);
        [cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small, Z.add_0_r by lia; reflexivity
        | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia | lia |].
      exact (val_mem_of_rdword segs (w_H W) mem _ _ S48).
  - apply pairwise_disjoint_of_extents.
    unfold extent_of_region, FM_L24, FM_L48.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | lia].
  - unfold FM_FACTS, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U22, U24, U26.
    rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; lia.
Qed.

End fe.

(* ------------------------------------------------------------------ *)
(* 5. The piece                                                        *)
(* ------------------------------------------------------------------ *)

Section fw. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Variable B : asyms.
Variable MT : ameter_ops.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world segs)
  (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word) (fp buf now : Z) (b fj : list byte)
  (TF : option TI.tframe) (Bw Bw' : list byte) (pos sp1 F : Z) (ly2 : alayout) (S2 : astate) (W2 : world segs)
  (mem2 : word -> option byte) (md2 : Model) (regs2 : bvmap 5 word).
Hypothesis LAWS0 : onann_laws B MT.
Hypothesis CALLEES : onann_callees B MT.
Hypothesis HFIX : onann_fix B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw'
  pos sp1 F.
Hypothesis HCUR : onann_fm_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs fp buf now sp1 Bw b pos F
  ly2 S2 W2 mem2 md2.
Hypothesis HREGS : onann_regs_fm regs regs2 fp sp1 F b.
Hypothesis DN : onann_dn_at B MT.

Local Abbreviation POST :=
  (@transport_onann_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' b).
Local Abbreviation AT pc R m md := (mkCfg (@YK11.mkst fx R (Z_to_bv 64 (BASE + pc)) m (YK11.seg_rom segs)) md).
Local Abbreviation fmU := (DSpec.ann_unknown (DSpec.fr_body b)).
Local Abbreviation fmMac := (TW.S_cfg_host_mac (onann_w1 timg_A Bw b)).

(* The bytes the piece may change: the bcmp wrapper's window below sp1 and the two slots. *)
Definition fm_Z (a : Z) : Prop :=
  (sp1 - 2 * ESTACK <= a < sp1) \/ (sp1 + 24 <= a < sp1 + 32) \/ (sp1 + 48 <= a < sp1 + 56).
Definition fm_KA (m : word -> option byte) : Prop :=
  forall a, 0 <= a < 2 ^ 64 -> ~ fm_Z a -> aview segs (w_H W2) m a = aview segs (w_H W2) mem2 a.
Definition fm_GA (m : word -> option byte) : Prop :=
  forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) m a.
(* The callee-saved registers the loop does not touch. *)
Definition fm_keep (R : bvmap 5 word) : Prop :=
  YK11.getr R (Z_to_bv 5 8) = YK11.getr regs2 (Z_to_bv 5 8) /\
  YK11.getr R (Z_to_bv 5 18) = YK11.getr regs2 (Z_to_bv 5 18) /\
  YK11.getr R (Z_to_bv 5 19) = YK11.getr regs2 (Z_to_bv 5 19) /\
  YK11.getr R (Z_to_bv 5 21) = YK11.getr regs2 (Z_to_bv 5 21) /\
  YK11.getr R (Z_to_bv 5 25) = YK11.getr regs2 (Z_to_bv 5 25) /\
  YK11.getr R (Z_to_bv 5 27) = YK11.getr regs2 (Z_to_bv 5 27).
Definition fm_J (m : word -> option byte) (md : Model) : Prop :=
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0
    ((ONANN_CID, pos) :: own) ly2 S2 W2 m md (k + 0).
(* The loop invariant at +0x2c8, turn i. *)
Definition fm_inv (i : Z) (R : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
  fm_J m md /\
  YK11.getr R (Z_to_bv 5 2) = w64 sp1 /\ YK11.getr R (Z_to_bv 5 3) = w64 (as_gp B) /\
  YK11.getr R (Z_to_bv 5 4) = w64 (as_tp B) /\ YK11.getr R (Z_to_bv 5 9) = w64 sp1 /\
  YK11.getr R (Z_to_bv 5 20) = w64 ONANN_S /\ YK11.getr R (Z_to_bv 5 22) = w64 15 /\
  YK11.getr R (Z_to_bv 5 23) = w64 (buf + 30) /\ YK11.getr R (Z_to_bv 5 24) = w64 i /\
  YK11.getr R (Z_to_bv 5 26) = w64 (i + 6) /\ fm_keep R /\
  rdword (aview segs (w_H W2) m) (sp1 + 24) = Some SHADOW_OFF /\
  rdword (aview segs (w_H W2) m) (sp1 + 48) = Some fp /\ fm_KA m /\ fm_GA m.
(* The state at +0x308, a3 = r. *)
Definition fm_out (r : Z) (R : bvmap 5 word) (m : word -> option byte) (md : Model) : Prop :=
  fm_J m md /\
  YK11.getr R (Z_to_bv 5 2) = w64 sp1 /\ YK11.getr R (Z_to_bv 5 3) = w64 (as_gp B) /\
  YK11.getr R (Z_to_bv 5 4) = w64 (as_tp B) /\ YK11.getr R (Z_to_bv 5 9) = w64 sp1 /\
  YK11.getr R (Z_to_bv 5 20) = w64 ONANN_S /\ YK11.getr R (Z_to_bv 5 22) = w64 fp /\
  YK11.getr R (Z_to_bv 5 24) = w64 SHADOW_OFF /\ YK11.getr R (Z_to_bv 5 13) = w64 r /\
  fm_keep R /\ fm_KA m /\ fm_GA m.

(* ---- facts at the cut ---- *)

Lemma fm_sp1 : spZ regs - 224 <= sp1 <= spZ regs - 192 /\ sp1 mod 32 = 0.
Proof.
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 &
    Hm & HTF & Htfg & Hrom & Hap & Hri0 & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  rewrite Esp1. assert (HFR : ONANN_FRAME = 192) by reflexivity. rewrite HFR.
  pose proof (Z.div_mod (spZ regs - 192) 32 ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound (spZ regs - 192) 32 ltac:(lia)) as M.
  set (q := (spZ regs - 192) / 32) in *. set (r := (spZ regs - 192) mod 32) in *.
  split; [lia|]. rewrite Z.mul_comm, Z.mod_mul by lia. reflexivity.
Qed.

Lemma fm_stk : sp0 mod 16 = 0 /\ alloc_ceiling <= sp0 - STK /\ sp0 <= 2 ^ 47 /\
  sp0 - STK <= spZ regs - ONANN_STK /\ spZ regs <= sp0.
Proof.
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & _).
  pose proof HJ0 as (HSTK & _ & (memS & HJi & _) & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
  pose proof Hstk as (Hsp0a & _ & Hceil & Hslo & Hshi & H47 & _).
  split; [exact Hsp0a|]. split; [lia|]. split; [lia|]. split; lia.
Qed.

(* The arithmetic every lemma below uses. *)
Lemma fm_arith : ONANN_STK = 8992 /\ ESTACK = 4096 /\ alloc_ceiling + 576 <= sp1 - 2 * ESTACK /\
  sp1 + 192 <= spZ regs /\ spZ regs - ONANN_STK <= sp1 - 2 * ESTACK /\ spZ regs <= sp0 /\
  sp0 - STK <= sp1 - 2 * ESTACK /\ sp1 + 64 <= sp0 /\ sp0 <= 2 ^ 47 /\ (sp1 - sp0) mod 16 = 0 /\ sp1 mod 32 = 0.
Proof.
  pose proof fm_sp1 as (Hs1 & Hs32). pose proof fm_stk as (Hsp0a & Hceil & H47 & Hlo & Hhi).
  assert (HSTKv : ONANN_STK = 8992) by reflexivity.
  assert (EST : ESTACK = 4096) by reflexivity.
  repeat split; try lia; apply fm_mod16; assumption.
Qed.

(* The frame F lies below alloc_ceiling. *)
Lemma fm_frame : 4096 <= F /\ F + 1024 <= alloc_ceiling /\ F mod 64 = 0.
Proof.
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 &
    Hm & HTF & Htfg & Hrom & Hap & Hri0 & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  unfold ONANN_FBYTES in HFc. split; [exact HF0|]. split; [exact HFc | exact HF64].
Qed.

(* The body bytes at buf + 30 .. + 44 at the cut: placed, read as the model's unknown, off the call's window; fp's
   range; and host_mac at s through the world relation at W1. *)
Lemma fm_buf :
  decode_rd_ok W2 mem2 (buf + 30) 15 /\
  (forall j, 0 <= j < 15 -> aview segs (w_H W2) mem2 (buf + 30 + j) = Some (DSpec.at8 fmU (Z.to_nat j))) /\
  (forall a, buf + 30 <= a < buf + 45 -> a < spZ regs - ONANN_STK \/ spZ regs <= a) /\
  (forall j, 0 <= j < 6 -> aview segs (w_H W2) mem2 (ONANN_S + j) = Some (DSpec.at8 fmMac (Z.to_nat j))) /\
  0 < fp /\ fp + 64 <= 2 ^ 63 /\ 33 <= DSpec.fr_body_len b.
Proof.
  pose proof LAWS0 as (HSMc & HCELLS & HZC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 &
    Hm & HTF & Htfg & Hrom & Hap & Hri0 & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HCUR as (HCUR0 & Htw2 & Hign & Hcmd & Haok & Hslots).
  pose proof HCUR0 as (HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
  destruct (onann_cur_ar B MT LAWS HFIX HCUR0) as (HARc & HAR2 & ELO & EHI & EFA & _).
  pose proof Hdf as (Hcode & Hbuf0 & Hgb & Hsrc & Hoffb & HnGb & Hfp0 & Hfp8 & Hfj & Hgf & Hinf & Hrdf & Hofff).
  destruct (OAL.oa_body_len b Hcode) as (Hbl0 & Hbl & Hblen).
  assert (Hac : DSpec.ann_code (DSpec.fr_cmd b) (DSpec.fr_body_len b) = 0).
  { unfold onann_ign in Hign. apply negb_false_iff in Hign. apply Z.eqb_eq in Hign. exact Hign. }
  destruct (OAL.oa_cmd_ok _ _ Hac) as (_ & H33).
  destruct (onann_src_kept B LAWS HROU HRNE lyc Sc W memc mdc ly2 S2 W2 mem2 md2 pos (spZ regs - ONANN_STK)
    (spZ regs) (onann_wr Bw b) buf (Z.of_nat (length b)) HARc HAR2 Hfrs Hperm EFA ELO EHI HK (onann_wr_G Bw b)
    HnGb Hoffb Hsrc ltac:(lia)) as (Hsrc2 & KV).
  pose proof (trans_src_ok_rd B LAWS ly2 S2 W2 mem2 md2 buf (Z.of_nat (length b)) HAR2 Hsrc2 ltac:(lia)) as Hrd.
  pose proof Hrdf as (_ & _ & _ & _ & Hfpq0 & Hfp63).
  split; [exact (trans_rd_ok_sub W2 mem2 buf (Z.of_nat (length b)) (buf + 30) 15 Hrd ltac:(lia) ltac:(lia)
    ltac:(lia))|].
  split.
  { intros j Hj. rewrite (KV (buf + 30 + j) ltac:(lia)).
    assert (Hlt : (Z.to_nat (30 + j) < length (TW.zs b))%nat) by (unfold TW.zs; rewrite length_map; lia).
    pose proof (garr8_mbyte tfibsegs _ buf (TW.zs b) (Z.to_nat (30 + j)) Hgb Hlt) as Hm1.
    rewrite Z2Nat.id in Hm1 by lia. replace (buf + (30 + j)) with (buf + 30 + j) in Hm1 by lia.
    unfold aview. rewrite Hm1. cbn [option_map]. f_equal.
    rewrite (fm_u_at b (Z.to_nat j) ltac:(lia) H33).
    rewrite (nth_indep (TW.zs b) 0 (bv_unsigned (Z_to_bv 8 0))) by (unfold TW.zs; rewrite length_map; lia).
    unfold TW.zs. rewrite map_nth. rewrite Z_to_bv_bv_unsigned.
    replace (Z.to_nat (30 + j)) with (30 + Z.to_nat j)%nat by lia. reflexivity. }
  split.
  { intros a Ha. unfold decode_off_win in Hoffb. lia. }
  split.
  { intros j Hj. destruct Htw2 as [_ HR].
    pose proof (HR TW.OFF_g_s TA_g_s TW.SZ_g_s j TMAP_A_g_s ltac:(unfold TW.SZ_g_s; lia)) as Hb.
    unfold ONANN_S. rewrite Hb. f_equal. rewrite fm_mac_eq.
    unfold DSpec.at8, DSpec.bz, DSpec.b8, TW.sub.
    rewrite fm_nth_firstn by lia. rewrite fm_nth_skipn.
    replace (Z.to_nat (TW.OFF_g_s + j)) with (Z.to_nat 1648 + Z.to_nat j)%nat by (unfold TW.OFF_g_s; lia).
    reflexivity. }
  unfold FRAME_F_SIZE in Hfp63. split; [lia|]. split; [lia | exact H33].
Qed.

(* ---- the cut's facts at a later memory of the piece ---- *)

Lemma fm_cur_move : forall m3 md3, fm_J m3 md3 -> fm_KA m3 -> fm_GA m3 ->
  onann_cur B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw b pos F ly2 S2 W2 m3 md3 0.
Proof.
  intros m3 md3 HJ3 KA GA.
  pose proof LAWS0 as (HSMc & HCELLS & HZC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
  pose proof HFIX as (HJ0 & _).
  pose proof HCUR as (HCUR0 & _).
  pose proof HCUR0 as (HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
  pose proof fm_arith as (HSTKv & EST & Hce & Hs1 & Hwl & Hhi & Hw0 & Hs64 & H47 & Hal & Hs32).
  pose proof fm_frame as (HF0 & HFc & HF64).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ0) as HARc.
  unfold ONANN_FBYTES in HFLw.
  refine (conj HJ3 (conj He0 (conj Hfrs (conj Hperm (conj HlyF (conj Hmo (conj _ (conj _ _)))))))).
  - apply (dk_kept_step_gw segs B LAWS transport_segs_low TG.G_HARNESS lyc Sc W memc mdc W2 mem2 m3
      (spZ regs - ONANN_STK) (spZ regs) (onann_wr Bw b) fm_Z HARc HK KA GA).
    + intros a Ha Hc. unfold fm_Z in Ha. lia.
    + intros b0 m0 i Hb Hi Ha. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b0 m0 HARc Hb) as (_ & H4096 & Hbc & _).
      unfold fm_Z in Ha. lia.
    + intros a Ha Hi _ _ _. exfalso. pose proof (transport_segs_low a Hi) as Hl. unfold kLowMemEnd in Hl.
      unfold fm_Z in Ha. lia.
    + intros cid p a Hin Hr Ha. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid p HARc Hin) as (G4096 & Gce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      unfold fm_Z in Ha.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid p) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid p + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia.
  - assert (HSo : forall o, In o ONANN_SAVED -> 8 <= fst o <= 104).
    { intros o Ho. unfold ONANN_SAVED in Ho. cbn [In] in Ho.
      repeat (destruct Ho as [<- | Ho]; [cbn [fst]; lia|]). destruct Ho. }
    rewrite Forall_forall in Hsaved |- *. intros o Ho. pose proof (HSo o Ho) as Hob.
    apply (fm_rdmove (aview segs (w_H W2) mem2)); [|exact (Hsaved o Ho)].
    intros i Hi. apply KA; [lia | unfold fm_Z; lia].
  - unfold ONANN_FBYTES. apply (fm_rdmove (aview segs (w_H W2) mem2)); [|exact HFLw].
    intros i Hi. apply KA; [lia | unfold fm_Z; lia].
Qed.

(* ---- the exit: +0x308, onann_dn_at ---- *)

Lemma fm_exit : forall R3 m3 md3, fm_out (TSS.find_mac_m fmU 15 fmMac) R3 m3 md3 ->
  SRr segs W2 (AT ONANN_DN R3 m3 md3) POST.
Proof.
  intros Rx m3 md3 (HJ3 & X2 & X3 & X4 & X9 & X20 & X22 & X24 & X13 & (K8 & K18 & K19 & K21 & K25 & K27) & KA & GA).
  pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 &
    Hm & HTF & Htfg & Hrom & Hap & Hri0 & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
  pose proof HCUR as (HCUR0 & Htw2 & Hign & Hcmd & Haok & Hslots).
  pose proof Haok as (Hav & Han & Ha24 & Ha32 & Hash).
  pose proof Hslots as (S56 & S0 & S32 & S40).
  pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R20 & R21 & R22 & R24 & R25 & R27).
  pose proof fm_arith as (HSTKv & EST & Hce & Hs1 & Hwl & Hhi' & Hw0 & Hs64 & H47 & Hal & Hs32).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  unfold ONANN_FBYTES in HFc.
  assert (HF8 : F / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
  assert (HF8' : 0 <= F / 8) by (apply Z.div_pos; lia).
  assert (KL : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W2) m3 a = aview segs (w_H W2) mem2 a)
    by (intros a Ha; apply KA; [lia | unfold fm_Z; lia]).
  apply (DN LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 m3 md3 Rx HFIX).
  - unfold onann_dn_cur.
    refine (conj (fm_cur_move m3 md3 HJ3 KA GA) (conj _ (conj Hign (conj _ _)))).
    + apply (tw_kept TMAP_A (aview segs (w_H W2) mem2)); [exact Htw2|].
      intros x Hx. pose proof (TMAP_A_hull x Hx) as Hh. unfold TG.G_HARNESS_LO, TG.G_HARNESS_HI in Hh.
      apply KL. lia.
    + unfold onann_a_ok. refine (conj _ (conj _ (conj _ (conj _ _)))).
      * apply (fm_garr8_move _ mem2); [exact Hav|]. intros j Hj. rewrite length_map in Hj.
        pose proof (fm_field_len (skipn 15 (DSpec.fr_body b))) as Hl. apply KL. unfold ONANN_A. lia.
      * apply (fm_garr8_move _ mem2); [exact Han|]. intros j Hj. rewrite length_map in Hj.
        pose proof (fm_field_len (skipn 24 (DSpec.fr_body b))) as Hl. apply KL. unfold ONANN_A. lia.
      * apply (fm_rdmove (aview segs (w_H W2) mem2)); [|exact Ha24].
        intros i Hi. apply KL. unfold ONANN_A. lia.
      * apply (fm_rdmove (aview segs (w_H W2) mem2)); [|exact Ha32].
        intros i Hi. apply KL. unfold ONANN_A. lia.
      * intros i Hi. rewrite KL; [exact (Hash i Hi)|]. unfold SHADOW_OFF. lia.
    + unfold onann_slots_dn, onann_slot in *. refine (conj _ (conj _ (conj _ _))).
      * apply (fm_rdmove (aview segs (w_H W2) mem2)); [|exact S56].
        intros i Hi. apply KA; [lia | unfold fm_Z; lia].
      * apply (fm_rdmove (aview segs (w_H W2) mem2)); [|exact S0].
        intros i Hi. apply KA; [lia | unfold fm_Z; lia].
      * apply (fm_rdmove (aview segs (w_H W2) mem2)); [|exact S32].
        intros i Hi. apply KA; [lia | unfold fm_Z; lia].
      * apply (fm_rdmove (aview segs (w_H W2) mem2)); [|exact S40].
        intros i Hi. apply KA; [lia | unfold fm_Z; lia].
  - unfold onann_regs_dn, onann_regs_fm, onann_regs_base.
    refine (conj (conj (conj X2 (conj _ (conj _ (conj (eq_trans K8 R8) (conj X9 (conj (eq_trans K18 R18)
      (eq_trans K19 R19))))))) (conj X20 (conj (eq_trans K21 R21) (conj X22 (conj X24 (conj (eq_trans K25 R25)
      (eq_trans K27 R27))))))) _).
    + exact (eq_trans X3 (eq_sym Hgp)).
    + exact (eq_trans X4 (eq_sym Htp)).
    + refine (eq_trans X13 _). f_equal. unfold onann_off. rewrite Hcmd, Z.eqb_refl. reflexivity.
Qed.

(* ---- one turn of the loop, from +0x2c8 ---- *)

Lemma fm_turn : forall i R m md, 0 <= i <= 9 -> fm_inv i R m md ->
  (TS0.memeq 6 (skipn (Z.to_nat i) fmU) fmMac = true ->
     forall R3 m3 md3, fm_out i R3 m3 md3 -> SRr segs W2 (AT ONANN_DN R3 m3 md3) POST) ->
  (TS0.memeq 6 (skipn (Z.to_nat i) fmU) fmMac = false -> i <= 8 ->
     forall R3 m3 md3, fm_inv (i + 1) R3 m3 md3 -> SRr segs W2 (AT FM_LP R3 m3 md3) POST) ->
  (TS0.memeq 6 (skipn (Z.to_nat i) fmU) fmMac = false -> i = 9 ->
     forall R3 m3 md3, fm_out (-1) R3 m3 md3 -> SRr segs W2 (AT ONANN_DN R3 m3 md3) POST) ->
  SRr segs W2 (AT FM_LP R m md) POST.
Proof.
intros i R m md Hi HINV XM XN XL.
destruct HINV as (HJ & R2 & R3 & R4 & R9 & R20 & R22 & R23 & R24 & R26 & (K8 & K18 & K19 & K21 & K25 & K27) & S24 &
  S48 & KA & GA).
pose proof LAWS0 as (HSMc & HCELLS & HZC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof CALLEES as (HSMR & HLEAF & HPFN & HBC & _).
pose proof fm_arith as (HSTKv & EST & Hce & Hs1 & Hwl & Hhi & Hw0 & Hs64 & H47 & Hal & Hs32).
pose proof fm_buf as (Hrd2 & Hub & Hbw & Hmac & Hfp0 & Hfp63 & H33).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hrd2 as (_ & _ & _ & _ & Hb30 & Hb63).
unfold fm_J in HJ.
(* +0x2c8 .. +0x2d8: a0 = buf + 30 + i, a2 = 6, a1 = s, the call of the bcmp wrapper *)
pose proof (fm_entryL W2 R m FM_LP sp1 fp i R9 R22 R24 R26 Hi ltac:(lia) ltac:(lia) ltac:(lia) S24 S48) as HS.
set (E := fm_EL R fp) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, fm_EL; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr R r)
  by (intros n r Hn; unfold E, fm_EL; apply ew_Eimg_Ereg_nat; exact Hn).
assert (SHOK : sh_ok segs FM_Bx (@nil shent) E (mrestrict (w_H W2) m)) by constructor.
pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transport)) as BR.
paj_run_tok RUN HS HJ SHOK FM_B0.
{ fm_awr0. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md1 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md1; clear mt end.
lazymatch type of HS with context [restrict _ ?mz] => rename mz into msC end.
assert (KD1 : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msC) a = aview segs (w_H W2) m a).
{ intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
  intros b0 wlo whi x Hiw Hx. cbv beta. fm_win Hiw Hx ltac:(lia). }
assert (GA1 : forall a, apresent (w_H W2) m a -> apresent (w_H W2) (ms_mem msC) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
clear HF HFr HG.
fm_reg HS (Z_to_bv 5 10) (w64 (buf + 30 + i)) Q10
  ltac:(rewrite (fm_a0 E (buf + 30) (i + 6) (eq_trans (EE 23%nat (Z_to_bv 5 23) eq_refl) R23)
          (eq_trans (EE 26%nat (Z_to_bv 5 26) eq_refl) R26) ltac:(lia) ltac:(lia)); f_equal; lia).
fm_reg HS (Z_to_bv 5 11) (w64 ONANN_S) Q11
  ltac:(cbn [sv_denot]; rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R20).
fm_reg HS (Z_to_bv 5 12) (w64 6) Q12 ltac:(reflexivity).
fm_reg HS (Z_to_bv 5 1) (Z_to_bv 64 (BASE + 27372)) Q1 ltac:(apply codeptr_val; exact HEI).
fm_kreg HS EE (Z_to_bv 5 2) 2%nat R2 Q2. fm_kreg HS EE (Z_to_bv 5 3) 3%nat R3 Q3.
fm_kreg HS EE (Z_to_bv 5 4) 4%nat R4 Q4. fm_kreg HS EE (Z_to_bv 5 9) 9%nat R9 Q9.
fm_kreg HS EE (Z_to_bv 5 20) 20%nat R20 Q20. fm_kreg HS EE (Z_to_bv 5 22) 22%nat R22 Q22.
fm_kreg HS EE (Z_to_bv 5 23) 23%nat R23 Q23. fm_kreg HS EE (Z_to_bv 5 24) 24%nat R24 Q24.
fm_kreg HS EE (Z_to_bv 5 26) 26%nat R26 Q26.
fm_kreg HS EE (Z_to_bv 5 8) 8%nat K8 Q8. fm_kreg HS EE (Z_to_bv 5 18) 18%nat K18 Q18.
fm_kreg HS EE (Z_to_bv 5 19) 19%nat K19 Q19. fm_kreg HS EE (Z_to_bv 5 21) 21%nat K21 Q21.
fm_kreg HS EE (Z_to_bv 5 25) 25%nat K25 Q25. fm_kreg HS EE (Z_to_bv 5 27) 27%nat K27 Q27.
assert (QSP : spZ (ms_regs msC) = sp1)
  by (change (bv_unsigned (YK11.getr (ms_regs msC) (Z_to_bv 5 2)) = sp1); rewrite Q2; unfold w64;
      apply unsigned_lit_small; lia).
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (transport_sigma TS___interceptor_trampoline_bcmp)) mm rom)
    mdx) Qx) end.
(* the two ranges at the call memory *)
assert (KC : forall a, 0 <= a < 2 ^ 64 -> ~ fm_Z a -> aview segs (w_H W2) (ms_mem msC) a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (KD1 a Ha); exact (KA a Ha Hn)).
assert (Hrd_C : decode_rd_ok W2 (ms_mem msC) (buf + 30) 15).
{ apply (trans_rd_ok_view W2 W2 mem2 (ms_mem msC) (buf + 30) 15 Hrd2).
  - intros a Ha. apply KC; [lia | unfold fm_Z; destruct (Hbw a ltac:(lia)); lia].
  - intros s Hs. apply KC; [lia | unfold fm_Z; lia]. }
pose proof (trans_rd_ok_sub W2 (ms_mem msC) (buf + 30) 15 (buf + 30 + i) 6 Hrd_C ltac:(lia) ltac:(lia) ltac:(lia))
  as (Vx & RAx & HHx & AMx & Hx0 & Hx63).
assert (Vy : forall j, 0 <= j < 6 -> aview segs (w_H W2) (ms_mem msC) (ONANN_S + j) = Some (DSpec.at8 fmMac (Z.to_nat j))).
{ intros j Hj. rewrite KC; [exact (Hmac j Hj) | unfold ONANN_S, TA_g_s; lia | unfold fm_Z, ONANN_S, TA_g_s; lia]. }
assert (Ux : forall j, 0 <= j < 15 -> aview segs (w_H W2) (ms_mem msC) (buf + 30 + j) = Some (DSpec.at8 fmU (Z.to_nat j))).
{ intros j Hj. rewrite KC; [exact (Hub j Hj) | lia | unfold fm_Z; destruct (Hbw (buf + 30 + j) ltac:(lia)); lia]. }
pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARC.
destruct (decode_zshadow_ra B ly2 S2 W2 (ms_mem msC) md1 ONANN_S (ONANN_S + TW.SZ_g_s) ONANN_S 6 HARC HZC
  ltac:(lia) ltac:(apply Z.leb_le; reflexivity) ltac:(apply Z.leb_le; reflexivity)) as (RAy & HHy).
(* the call of the bcmp wrapper *)
eapply SRr_bind.
{ apply (fm_bcmp B LAWS STK sp0 FP ly S W0 mem0 md0 ((ONANN_CID, pos) :: own) ly2 S2 W2 (ms_mem msC) md1 (k + 0)
    (ms_regs msC) (buf + 30 + i) ONANN_S 6 (sp1 - sp0) (Z_to_bv 64 (BASE + 27372)) (HBC fx) HJ Q10 Q11 Q12).
  - lia.
  - lia.
  - lia.
  - unfold ONANN_S, TA_g_s; lia.
  - unfold ONANN_S, TA_g_s; lia.
  - rewrite QSP; lia.
  - exact Hal.
  - lia.
  - lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply (ret_ok_codeptr_v (PI := PI_transport)); [lia | reflexivity].
  - intros a Ha. split; [apply Vx; lia|]. rewrite QSP. destruct (Hbw a ltac:(lia)); lia.
  - intros a Ha. split.
    + replace a with (ONANN_S + (a - ONANN_S)) by lia. rewrite (Vy (a - ONANN_S) ltac:(lia)). discriminate.
    + rewrite QSP. unfold ONANN_S, TA_g_s in *. lia.
  - intros a Ha. destruct (Hbw a ltac:(lia)); lia.
  - intros a Ha. unfold ONANN_S, TA_g_s in *. lia.
  - exact AMx.
  - unfold amem_range, ONANN_S, TA_g_s, kLowMemEnd. left. lia.
  - exact RAx.
  - intros _. exact HHx.
  - exact RAy.
  - intros _. exact HHy. }
cbv beta. intros W3 c3 _ (-> & RB & mB & mdB & -> & HJB & v & HPB & HvB & Hcmp & HfrB & HgrB).
assert (KB : forall a, 0 <= a < 2 ^ 64 -> ~ (sp1 - 2 * ESTACK <= a < sp1) ->
  aview segs (w_H W2) mB a = aview segs (w_H W2) (ms_mem msC) a)
  by (intros a Ha Hn; apply HfrB; [exact Ha | lia]).
assert (KBZ : forall a, 0 <= a < 2 ^ 64 -> ~ fm_Z a -> aview segs (w_H W2) mB a = aview segs (w_H W2) mem2 a)
  by (intros a Ha Hn; rewrite (KB a Ha ltac:(unfold fm_Z in Hn; lia)); exact (KC a Ha Hn)).
assert (GAB : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) mB a)
  by (intros a Ha; exact (HgrB a (GA1 a (GA a Ha)))).
assert (SB24 : rdword (aview segs (w_H W2) mB) (sp1 + 24) = Some SHADOW_OFF).
{ apply (fm_rdmove (aview segs (w_H W2) m)); [|exact S24].
  intros j Hj. rewrite (KB (sp1 + 24 + j) ltac:(lia) ltac:(lia)). apply KD1. lia. }
assert (SB48 : rdword (aview segs (w_H W2) mB) (sp1 + 48) = Some fp).
{ apply (fm_rdmove (aview segs (w_H W2) m)); [|exact S48].
  intros j Hj. rewrite (KB (sp1 + 48 + j) ltac:(lia) ltac:(lia)). apply KD1. lia. }
assert (B2 : YK11.getr RB (Z_to_bv 5 2) = w64 sp1) by (rewrite (HPB 2 ltac:(hnf; lia)); exact Q2).
assert (B3 : YK11.getr RB (Z_to_bv 5 3) = w64 (as_gp B)) by (rewrite (HPB 3 ltac:(hnf; lia)); exact Q3).
assert (B4 : YK11.getr RB (Z_to_bv 5 4) = w64 (as_tp B)) by (rewrite (HPB 4 ltac:(hnf; lia)); exact Q4).
assert (B9 : YK11.getr RB (Z_to_bv 5 9) = w64 sp1) by (rewrite (HPB 9 ltac:(hnf; lia)); exact Q9).
assert (B20 : YK11.getr RB (Z_to_bv 5 20) = w64 ONANN_S) by (rewrite (HPB 20 ltac:(hnf; lia)); exact Q20).
assert (B22 : YK11.getr RB (Z_to_bv 5 22) = w64 15) by (rewrite (HPB 22 ltac:(hnf; lia)); exact Q22).
assert (B23 : YK11.getr RB (Z_to_bv 5 23) = w64 (buf + 30)) by (rewrite (HPB 23 ltac:(hnf; lia)); exact Q23).
assert (B24 : YK11.getr RB (Z_to_bv 5 24) = w64 i) by (rewrite (HPB 24 ltac:(hnf; lia)); exact Q24).
assert (B26 : YK11.getr RB (Z_to_bv 5 26) = w64 (i + 6)) by (rewrite (HPB 26 ltac:(hnf; lia)); exact Q26).
assert (B8 : YK11.getr RB (Z_to_bv 5 8) = YK11.getr regs2 (Z_to_bv 5 8)) by (rewrite (HPB 8 ltac:(hnf; lia)); exact Q8).
assert (B18 : YK11.getr RB (Z_to_bv 5 18) = YK11.getr regs2 (Z_to_bv 5 18))
  by (rewrite (HPB 18 ltac:(hnf; lia)); exact Q18).
assert (B19 : YK11.getr RB (Z_to_bv 5 19) = YK11.getr regs2 (Z_to_bv 5 19))
  by (rewrite (HPB 19 ltac:(hnf; lia)); exact Q19).
assert (B21 : YK11.getr RB (Z_to_bv 5 21) = YK11.getr regs2 (Z_to_bv 5 21))
  by (rewrite (HPB 21 ltac:(hnf; lia)); exact Q21).
assert (B25 : YK11.getr RB (Z_to_bv 5 25) = YK11.getr regs2 (Z_to_bv 5 25))
  by (rewrite (HPB 25 ltac:(hnf; lia)); exact Q25).
assert (B27 : YK11.getr RB (Z_to_bv 5 27) = YK11.getr regs2 (Z_to_bv 5 27))
  by (rewrite (HPB 27 ltac:(hnf; lia)); exact Q27).
(* +0x2dc: `beqz a0`, from a fresh state *)
clear HS SHOK.
change (Z_to_bv 64 (BASE + 27372)) with (Z_to_bv 64 (BASE + FM_RA)).
pose proof (fm_entryL W2 RB mB FM_RA sp1 fp i B9 B22 B24 B26 Hi ltac:(lia) ltac:(lia) ltac:(lia) SB24 SB48) as HS.
set (E2 := fm_EL RB fp) in HS.
assert (HEI2 : img_env VAL A_LIM E2) by (unfold E2, fm_EL; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2 n = YK11.getr RB r)
  by (intros n r Hn; unfold E2, fm_EL; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E2_32 : ew E2 32 = w64 fp)
  by (unfold E2, fm_EL; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra RB _ 0)).
assert (SHOK : sh_ok segs FM_Bx (@nil shent) E2 (mrestrict (w_H W2) mB)) by constructor.
assert (D10 : sv_denot E2 (SOff 10 0) = v)
  by (cbn [sv_denot]; rewrite (EE2 10%nat (Z_to_bv 5 10) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact HvB).
assert (IFF : TS0.memeq 6 (skipn (Z.to_nat i) fmU) fmMac = true <-> v = w64 0).
{ pose proof (fm_memeq_iff fmU fmMac i (aview segs (w_H W2) (ms_mem msC)) (buf + 30) ONANN_S ltac:(lia) ltac:(lia)
    Ux Vy) as MI.
  split; [intros H; apply (proj2 Hcmp); apply (proj1 MI); exact H
         | intros H; apply (proj2 MI); exact (proj1 Hcmp H)]. }
psrr_branch_tok RUN BR HS SHOK FM_B0.
- (* a0 = 0: the 6 bytes agree; a3 = i, s8 and s6 reloaded, to +0x308 *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc. change (sv_denot E2 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  pose proof (fm_eqz v Hc) as Hv0.
  assert (Hmeq : TS0.memeq 6 (skipn (Z.to_nat i) fmU) fmMac = true) by (apply IFF; exact Hv0).
  paj_run_to_tok RUNTO HS HJB SHOK FM_B0 ONANN_DN.
  { fm_awr0. }
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    set (md3 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md3; clear mt end.
  lazymatch type of HS with context [restrict _ ?mz] => rename mz into msF end.
  assert (KDF : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msF) a = aview segs (w_H W2) mB a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hiw Hx. cbv beta. fm_win Hiw Hx ltac:(lia). }
  assert (GAF : forall a, apresent (w_H W2) mB a -> apresent (w_H W2) (ms_mem msF) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  fm_reg HS (Z_to_bv 5 13) (w64 i) Y13
    ltac:(cbn [sv_denot]; rewrite (EE2 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact B24).
  fm_reg HS (Z_to_bv 5 22) (w64 fp) Y22
    ltac:(cbn [sv_denot]; rewrite E2_32; unfold w64; rewrite unsigned_lit_small, Z.add_0_r by lia; reflexivity).
  fm_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
  fm_kreg HS EE2 (Z_to_bv 5 2) 2%nat B2 Y2. fm_kreg HS EE2 (Z_to_bv 5 3) 3%nat B3 Y3.
  fm_kreg HS EE2 (Z_to_bv 5 4) 4%nat B4 Y4. fm_kreg HS EE2 (Z_to_bv 5 9) 9%nat B9 Y9.
  fm_kreg HS EE2 (Z_to_bv 5 20) 20%nat B20 Y20.
  fm_kreg HS EE2 (Z_to_bv 5 8) 8%nat B8 Y8. fm_kreg HS EE2 (Z_to_bv 5 18) 18%nat B18 Y18.
  fm_kreg HS EE2 (Z_to_bv 5 19) 19%nat B19 Y19. fm_kreg HS EE2 (Z_to_bv 5 21) 21%nat B21 Y21.
  fm_kreg HS EE2 (Z_to_bv 5 25) 25%nat B25 Y25. fm_kreg HS EE2 (Z_to_bv 5 27) 27%nat B27 Y27.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
    change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_DN)) mm rom) mdx) Qx) end.
  apply (XM Hmeq (ms_regs msF) (ms_mem msF) md3).
  refine (conj HJB (conj Y2 (conj Y3 (conj Y4 (conj Y9 (conj Y20 (conj Y22 (conj Y24 (conj Y13
    (conj (conj Y8 (conj Y18 (conj Y19 (conj Y21 (conj Y25 Y27))))) (conj _ _))))))))))).
  + intros a Ha Hn. rewrite (KDF a Ha). exact (KBZ a Ha Hn).
  + intros a Ha. exact (GAF a (GAB a Ha)).
- (* a0 <> 0: the 6 bytes differ; s10 + 1, s8 + 1, `bgeu s6, s10` *)
  cbn [branch_taken] in Hc. rewrite D10 in Hc. change (sv_denot E2 (SLit 0)) with (Z_to_bv 64 0) in Hc.
  assert (Hmf : TS0.memeq 6 (skipn (Z.to_nat i) fmU) fmMac = false).
  { apply Bool.not_true_is_false. intros EM.
    pose proof (proj1 IFF EM) as Hv0. rewrite Hv0 in Hc. unfold w64, bv_eqb in Hc.
    rewrite Z.eqb_refl in Hc. discriminate Hc. }
  clear Hc.
  paj_run_tok RUN HS HJB SHOK FM_B0.
  { fm_awr0. }
  lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
    set (md4 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md4; clear mt end.
  lazymatch type of HS with context [restrict _ ?mz] => rename mz into msD end.
  assert (KDD : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msD) a = aview segs (w_H W2) mB a).
  { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
    intros b0 wlo whi x Hiw Hx. cbv beta. fm_win Hiw Hx ltac:(lia). }
  assert (GAD : forall a, apresent (w_H W2) mB a -> apresent (w_H W2) (ms_mem msD) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  assert (D22 : sv_denot E2 (SOff 22 0) = Z_to_bv 64 15)
    by (cbn [sv_denot]; rewrite (EE2 22%nat (Z_to_bv 5 22) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact B22).
  assert (D26 : sv_denot E2 (SOff 26 1) = Z_to_bv 64 (i + 7)).
  { cbn [sv_denot]. rewrite (EE2 26%nat (Z_to_bv 5 26) eq_refl), B26. unfold w64.
    rewrite unsigned_lit_small by lia. f_equal. lia. }
  psrr_branch_tok RUN BR HS SHOK FM_B0.
  + (* i + 7 <= 15: back to +0x2c8 with i + 1 *)
    cbn [branch_taken] in Hc. rewrite D22, D26 in Hc.
    assert (Hi8 : i <= 8).
    { unfold bv_ltu in Hc. rewrite !unsigned_lit_small in Hc by lia.
      apply negb_true_iff, Z.ltb_ge in Hc. lia. }
    paj_run_to_tok RUNTO HS HJB SHOK FM_B0 FM_LP.
    { fm_awr0. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (md5 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md5; clear mt end.
    lazymatch type of HS with context [restrict _ ?mz] => rename mz into msE end.
    assert (KDE : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msE) a = aview segs (w_H W2) (ms_mem msD) a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
      intros b0 wlo whi x Hiw Hx. cbv beta. fm_win Hiw Hx ltac:(lia). }
    assert (GAE : forall a, apresent (w_H W2) (ms_mem msD) a -> apresent (w_H W2) (ms_mem msE) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    fm_reg HS (Z_to_bv 5 24) (w64 (i + 1)) Y24
      ltac:(cbn [sv_denot]; rewrite (EE2 24%nat (Z_to_bv 5 24) eq_refl), B24; unfold w64;
            rewrite unsigned_lit_small by lia; reflexivity).
    fm_reg HS (Z_to_bv 5 26) (w64 (i + 1 + 6)) Y26
      ltac:(cbn [sv_denot]; rewrite (EE2 26%nat (Z_to_bv 5 26) eq_refl), B26; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia).
    fm_kreg HS EE2 (Z_to_bv 5 2) 2%nat B2 Y2. fm_kreg HS EE2 (Z_to_bv 5 3) 3%nat B3 Y3.
    fm_kreg HS EE2 (Z_to_bv 5 4) 4%nat B4 Y4. fm_kreg HS EE2 (Z_to_bv 5 9) 9%nat B9 Y9.
    fm_kreg HS EE2 (Z_to_bv 5 20) 20%nat B20 Y20. fm_kreg HS EE2 (Z_to_bv 5 22) 22%nat B22 Y22.
    fm_kreg HS EE2 (Z_to_bv 5 23) 23%nat B23 Y23.
    fm_kreg HS EE2 (Z_to_bv 5 8) 8%nat B8 Y8. fm_kreg HS EE2 (Z_to_bv 5 18) 18%nat B18 Y18.
    fm_kreg HS EE2 (Z_to_bv 5 19) 19%nat B19 Y19. fm_kreg HS EE2 (Z_to_bv 5 21) 21%nat B21 Y21.
    fm_kreg HS EE2 (Z_to_bv 5 25) 25%nat B25 Y25. fm_kreg HS EE2 (Z_to_bv 5 27) 27%nat B27 Y27.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + FM_LP)) mm rom) mdx) Qx) end.
    apply (XN Hmf Hi8 (ms_regs msE) (ms_mem msE) md5).
    refine (conj HJB (conj Y2 (conj Y3 (conj Y4 (conj Y9 (conj Y20 (conj Y22 (conj Y23 (conj Y24 (conj Y26
      (conj (conj Y8 (conj Y18 (conj Y19 (conj Y21 (conj Y25 Y27))))) (conj _ (conj _ (conj _ _)))))))))))))).
    * apply (fm_rdmove (aview segs (w_H W2) mB)); [|exact SB24].
      intros j Hj. rewrite (KDE (sp1 + 24 + j) ltac:(lia)). apply KDD. lia.
    * apply (fm_rdmove (aview segs (w_H W2) mB)); [|exact SB48].
      intros j Hj. rewrite (KDE (sp1 + 48 + j) ltac:(lia)). apply KDD. lia.
    * intros a Ha Hn. rewrite (KDE a Ha), (KDD a Ha). exact (KBZ a Ha Hn).
    * intros a Ha. exact (GAE a (GAD a (GAB a Ha))).
  + (* i + 7 > 15: i = 9, a3 = -1, to +0x308 *)
    cbn [branch_taken] in Hc. rewrite D22, D26 in Hc.
    assert (Hi9 : i = 9).
    { unfold bv_ltu in Hc. rewrite !unsigned_lit_small in Hc by lia.
      apply negb_false_iff, Z.ltb_lt in Hc. lia. }
    paj_run_to_tok RUNTO HS HJB SHOK FM_B0 ONANN_DN.
    { fm_awr0. }
    lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
      set (md5 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md5; clear mt end.
    lazymatch type of HS with context [restrict _ ?mz] => rename mz into msE end.
    assert (KDE : forall a, 0 <= a < 2 ^ 64 -> aview segs (w_H W2) (ms_mem msE) a = aview segs (w_H W2) (ms_mem msD) a).
    { intros a Ha. apply (kept_of_frame _ _ _ _ _ (fun _ => False) HFr); [| exact Ha | tauto].
      intros b0 wlo whi x Hiw Hx. cbv beta. fm_win Hiw Hx ltac:(lia). }
    assert (GAE : forall a, apresent (w_H W2) (ms_mem msD) a -> apresent (w_H W2) (ms_mem msE) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
    fm_reg HS (Z_to_bv 5 13) (w64 (-1)) Y13
      ltac:(cbn [sv_denot]; unfold w64; apply Z_to_bv64_eq_mod; reflexivity).
    fm_reg HS (Z_to_bv 5 22) (w64 fp) Y22
      ltac:(cbn [sv_denot]; rewrite E2_32; unfold w64; rewrite unsigned_lit_small, Z.add_0_r by lia; reflexivity).
    fm_reg HS (Z_to_bv 5 24) (w64 SHADOW_OFF) Y24 ltac:(reflexivity).
    fm_kreg HS EE2 (Z_to_bv 5 2) 2%nat B2 Y2. fm_kreg HS EE2 (Z_to_bv 5 3) 3%nat B3 Y3.
    fm_kreg HS EE2 (Z_to_bv 5 4) 4%nat B4 Y4. fm_kreg HS EE2 (Z_to_bv 5 9) 9%nat B9 Y9.
    fm_kreg HS EE2 (Z_to_bv 5 20) 20%nat B20 Y20.
    fm_kreg HS EE2 (Z_to_bv 5 8) 8%nat B8 Y8. fm_kreg HS EE2 (Z_to_bv 5 18) 18%nat B18 Y18.
    fm_kreg HS EE2 (Z_to_bv 5 19) 19%nat B19 Y19. fm_kreg HS EE2 (Z_to_bv 5 21) 21%nat B21 Y21.
    fm_kreg HS EE2 (Z_to_bv 5 25) 25%nat B25 Y25. fm_kreg HS EE2 (Z_to_bv 5 27) 27%nat B27 Y27.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
      change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + ONANN_DN)) mm rom) mdx) Qx) end.
    apply (XL Hmf Hi9 (ms_regs msE) (ms_mem msE) md5).
    refine (conj HJB (conj Y2 (conj Y3 (conj Y4 (conj Y9 (conj Y20 (conj Y22 (conj Y24 (conj Y13
      (conj (conj Y8 (conj Y18 (conj Y19 (conj Y21 (conj Y25 Y27))))) (conj _ _))))))))))).
    * intros a Ha Hn. rewrite (KDE a Ha), (KDD a Ha). exact (KBZ a Ha Hn).
    * intros a Ha. exact (GAE a (GAD a (GAB a Ha))).
Qed.

(* ---- the loop: induction on the turns left ---- *)

Lemma fm_loop : forall (n : nat) i R m md, 0 <= i -> i + Z.of_nat (Datatypes.S n) = 10 ->
  TSS.find_mac_m fmU 15 fmMac = TSS.find_mac_loop fmU fmMac i (Datatypes.S n) ->
  fm_inv i R m md -> SRr segs W2 (AT FM_LP R m md) POST.
Proof.
  induction n as [|n IH]; intros i R m md Hi0 Hin Hfm HINV.
  - apply (fm_turn i R m md ltac:(lia) HINV).
    + intros Hmeq R3 m3 md3 HO. apply fm_exit. rewrite Hfm, fm_find_S, Hmeq. exact HO.
    + intros _ Hle. lia.
    + intros Hmf _ R3 m3 md3 HO. apply fm_exit. rewrite Hfm, fm_find_S, Hmf. exact HO.
  - apply (fm_turn i R m md ltac:(lia) HINV).
    + intros Hmeq R3 m3 md3 HO. apply fm_exit. rewrite Hfm, fm_find_S, Hmeq. exact HO.
    + intros Hmf _ R3 m3 md3 HI. apply (IH (i + 1) R3 m3 md3 ltac:(lia) ltac:(lia)); [|exact HI].
      rewrite Hfm, fm_find_S, Hmf. reflexivity.
    + intros _ H9. lia.
Qed.

(* ---- the piece: run 1 to the loop head, then the loop ---- *)

Lemma fm_main : SRr segs W2 (AT ONANN_FM regs2 mem2 md2) POST.
Proof using All.
pose proof LAWS0 as (HSMc & HCELLS & HZC & HGU & HGNE & HROU & HRNE & LAWS & MTL & MTF & SMP & ASF & FFL & HGX & HGE).
pose proof HFIX as (HJ0 & Hret & Hra & Hgp & Htp & H10 & H11 & H12 & Hsp16 & Hlo & Hhi & Hnow & Hdf & Htw0 & Hgf0 &
  Hm & HTF & Htfg & Hrom & Hap & Hri0 & Hcnt & Hcnt2 & Hev & Esp1 & EF & HF0 & HF64 & HFc & HFapp).
pose proof HCUR as (HCUR0 & Htw2 & Hign & Hcmd & Haok & Hslots).
pose proof HCUR0 as (HJ2 & He0 & Hfrs & Hperm & HlyF & Hmo & HK & Hsaved & HFLw).
pose proof Haok as (Hav & Han & Ha24 & Ha32 & Hash).
pose proof Hslots as (S56 & S0 & S32 & S40).
pose proof HREGS as ((R2 & R3 & R4 & R8 & R9 & R18 & R19) & R20 & R21 & R22 & R24 & R25 & R27).
pose proof fm_arith as (HSTKv & EST & Hce & Hs1 & Hwl & Hhi' & Hw0 & Hs64 & H47 & Hal & Hs32).
pose proof fm_buf as (Hrd2 & Hub & Hbw & Hmac & Hfp0 & Hfp63 & H33).
pose proof fm_frame as (HF0' & HFc' & HF64').
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof Hrd2 as (_ & _ & _ & _ & Hb30 & Hb63).
pose proof HK as (_ & _ & _ & _ & _ & K6).
(* +0x2a8 .. +0x2c4, run 1 to the loop head *)
pose proof (fm_entry0 W2 regs2 mem2 sp1 F buf R9 R18 HF0 ltac:(lia) ltac:(lia) Hs32 ltac:(lia)
  ltac:(intros a Ha; apply K6; lia) ltac:(intros a Ha; apply K6; lia) S56 Ha24 Ha32) as HS.
set (E := fm_E0 regs2 buf) in HS.
assert (HEI : img_env VAL A_LIM E) by (unfold E, fm_E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs2 r)
  by (intros n r Hn; unfold E, fm_E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = sp1)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U18 : bv_unsigned (ew E 18) = F)
  by (rewrite (EE 18%nat 18%bv eq_refl), R18; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 (buf + 30))
  by (unfold E, fm_E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (SHOK : sh_ok segs FM_Bx (@nil shent) E (mrestrict (w_H W2) mem2)) by constructor.
pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
  as RUNTO.
paj_run_to_tok RUNTO HS HJ2 SHOK FM_B0 FM_LP.
{ lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fpq ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fpq b0 bc lyq ownq) end.
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
     left; split; [unfold awr_byte; left; lia | lia] |].
  apply awr_ok_x_cons;
    [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; rewrite U9 in Ha;
     left; split; [unfold awr_byte; left; lia | lia] |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_cons; [intros a Ha; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; lia |].
  apply awr_ok_x_nil. }
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing (m_vm_lazy ?m0) ?mt ?m0)) _ =>
  set (md1 := with_vm_backing (m_vm_lazy m0) mt m0) in *; clearbody md1; clear mt end.
lazymatch type of HS with context [restrict _ ?mz] => rename mz into msA end.
assert (KR1 : forall a, 0 <= a < 2 ^ 64 -> ~ ((sp1 + 24 <= a < sp1 + 32) \/ (sp1 + 48 <= a < sp1 + 56)) ->
  aview segs (w_H W2) (ms_mem msA) a = aview segs (w_H W2) mem2 a).
{ intros a Ha Hn. apply (kept_of_frame _ _ _ _ _ (fun x => (sp1 + 24 <= x < sp1 + 32) \/ (sp1 + 48 <= x < sp1 + 56))
    HFr); [| exact Ha | exact Hn].
  intros b0 wlo whi x Hiw Hx. cbv beta. fm_win Hiw Hx ltac:(rewrite ?U9, ?U18 in Hx; lia). }
assert (GA1 : forall a, apresent (w_H W2) mem2 a -> apresent (w_H W2) (ms_mem msA) a)
  by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
pose proof (st_ok_pi_region_nth _ _ _ 0 _ HS eq_refl) as RS0.
pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as RS1.
cbn [ms_mem restrict] in RS0, RS1.
clear HF HFr HG.
(* the two slots the run wrote *)
pose proof (can_field_of_region E (mrestrict (w_H W2) (ms_mem msA)) 9%nat sp1 _ _ _ _ _ 24 8 (SOff 24 0) SHADOW_OFF
  RS0 U9 ltac:(cbn [In]; left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite (EE 24%nat (Z_to_bv 5 24) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R24)
  ltac:(unfold SHADOW_OFF; change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(lia)) as V24.
pose proof (can_field_of_region E (mrestrict (w_H W2) (ms_mem msA)) 9%nat sp1 _ _ _ _ _ 48 8 (SOff 22 0) fp
  RS1 U9 ltac:(cbn [In]; left; reflexivity)
  ltac:(cbn [sv_denot]; rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned; exact R22)
  ltac:(change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia) ltac:(lia)) as V48.
pose proof (AF0x.val_mem_rdword (w_H W2) (ms_mem msA) (sp1 + 24) SHADOW_OFF ltac:(unfold SHADOW_OFF; lia) V24) as T24.
pose proof (AF0x.val_mem_rdword (w_H W2) (ms_mem msA) (sp1 + 48) fp ltac:(lia) V48) as T48.
(* the registers at +0x2c8 *)
fm_kreg HS EE (Z_to_bv 5 2) 2%nat R2 X2. fm_kreg HS EE (Z_to_bv 5 9) 9%nat R9 X9.
fm_kreg HS EE (Z_to_bv 5 20) 20%nat R20 X20.
fm_reg HS (Z_to_bv 5 3) (w64 (as_gp B)) X3
  ltac:(cbn [sv_denot]; rewrite (EE 3%nat (Z_to_bv 5 3) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R3 Hgp)).
fm_reg HS (Z_to_bv 5 4) (w64 (as_tp B)) X4
  ltac:(cbn [sv_denot]; rewrite (EE 4%nat (Z_to_bv 5 4) eq_refl), Z.add_0_r, Z_to_bv_bv_unsigned;
        exact (eq_trans R4 Htp)).
fm_reg HS (Z_to_bv 5 22) (w64 15) X22 ltac:(reflexivity).
fm_reg HS (Z_to_bv 5 23) (w64 (buf + 30)) X23
  ltac:(cbn [sv_denot]; rewrite E32; unfold w64; rewrite unsigned_lit_small, Z.add_0_r by lia; reflexivity).
fm_reg HS (Z_to_bv 5 24) (w64 0) X24 ltac:(reflexivity).
fm_reg HS (Z_to_bv 5 26) (w64 (0 + 6)) X26 ltac:(reflexivity).
fm_kreg0 HS EE regs2 (Z_to_bv 5 8) 8%nat X8. fm_kreg0 HS EE regs2 (Z_to_bv 5 18) 18%nat X18.
fm_kreg0 HS EE regs2 (Z_to_bv 5 19) 19%nat X19. fm_kreg0 HS EE regs2 (Z_to_bv 5 21) 21%nat X21.
fm_kreg0 HS EE regs2 (Z_to_bv 5 25) 25%nat X25. fm_kreg0 HS EE regs2 (Z_to_bv 5 27) 27%nat X27.
pmkst HS.
lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Qx =>
  change (SRr sg Wx (mkCfg (@YK11.mkst fx rg (Z_to_bv 64 (BASE + FM_LP)) mm rom) mdx) Qx) end.
apply (fm_loop 9 0 (ms_regs msA) (ms_mem msA) md1 ltac:(lia) ltac:(reflexivity)).
- unfold TSS.find_mac_m. reflexivity.
- refine (conj HJ2 (conj X2 (conj X3 (conj X4 (conj X9 (conj X20 (conj X22 (conj X23 (conj X24 (conj X26
    (conj (conj X8 (conj X18 (conj X19 (conj X21 (conj X25 X27))))) (conj T24 (conj T48 (conj _ _)))))))))))))).
  + intros a Ha Hn. apply KR1; [exact Ha|]. unfold fm_Z in Hn. tauto.
  + exact GA1.
Qed.

End fw.

(* The find_mac piece of the walk of on_announce (OnannCut.v onann_fm_stmt), at every machine, run ceiling, record
   and meter. *)
Theorem onann_piece_fm : forall fx rc B MT, @onann_fm_stmt fx rc B MT.
Proof.
  intros fx rc B MT. unfold onann_fm_stmt, onann_fm_at.
  intros DN LAWS0 CALLEES STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos sp1 F
    ly2 S2 W2 mem2 md2 regs2 HFIX HCUR HREGS.
  exact (@fm_main fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs fp buf now b fj TF Bw Bw' pos
    sp1 F ly2 S2 W2 mem2 md2 regs2 LAWS0 CALLEES HFIX HCUR HREGS DN).
Qed.

Print Assumptions onann_piece_fm.
