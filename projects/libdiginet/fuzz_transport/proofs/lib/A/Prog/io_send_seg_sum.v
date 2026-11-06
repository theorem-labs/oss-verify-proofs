(* io_send_seg_sum: the body-sum loop of the image-A walk of io_send (fuzz_transport.asan e89be137db17, entry
   0x82d60 = TImgA.v ti_io_send timg_A; the statement is lib/A/Prog/io_send_cg.v, whose header lines 98-99 measure
   this stretch): io_send + 0x2cc .. + 0x534 (0x8302c .. 0x83294), the end of the inlined spec_read_frame.
     +0x2cc .. +0x2d4  a1 = 0; `beqz a2` (a2 = f.body_len) to +0x52c; a0 = s1 + 30;
     +0x2d8 .. +0x300  turn i (a0 = a3 = p + 30 + i, a2 = body_len - i, a1 = the sum of the first i body bytes):
                       the instrumented check of the byte at a0 (shadow byte at (a0 >> 3) + s4; not 0 goes to the
                       slow path +0x304 .. +0x308, whose failure is the error path +0x30c, errpath_load1), the load of
                       p[30 + i] at a3, a1 + it, a0 and a3 one up, a2 one down; `bnez a2` back to +0x2d8, else `j`
                       to +0x52c;
     +0x52c .. +0x534  a0 = 0; the 2-byte store of a1 at sp + 80 (f + 72, the struct's body_sum); `j` to +0x314
                       (0x83074, where the parse's error arms join).
   How it is proved, in the shape of decode's DgnBcScan.v. Each run is a symbolic run of lib/A/Prog/PaShadow.v over
   the G journal (lib/A/Prog/TransportGRunA.v paj_run_x / paj_run_to_x) from a fresh state whose atoms are the
   registers at its pc:
     ios_sum_turn   turn i at +0x2d8: the body byte p[30 + i] as a read-only region at a3 (atom 32), and the shadow
                    entry of the byte at a0 (su_SH, from the frame's range_addressable: DgnTransportCg.v
                    decode_rd_ok), so the token engine decides the check and the error path is not reached; the
                    run leaves the memory as it was (YA0o.v frame_of_read_only); split on `bnez a2`;
     ios_sum_iter   the turns, by induction on body_len - i;
     ios_sum_loop   +0x2cc: split on `beqz a2`, then the turns from i = 0 with the sum 0;
     ios_sum_tail   +0x52c: the store, a byte of the journal's window [sp0 - STK, sp0) (awr_byte);
     ios_sum_seg    the stretch, self-contained, in continuation form.
   The sum: su_sum frame i is DgnSpec.v sum_bytes of the first i bytes of skipn 30 frame (sum_bytes_firstn_S gives
   one more byte, as lib/Prog/T/io_send_keep.v sum_bytes_sub_succ does for the plain walk); the 16 bits stored are
   DgnSpec.v fr_body_sum frame, which lib/A/Prog/io_send_seg_frm.v ios_fields equates with the struct's
   sf_body_sum (rf frame) at parse code 0. The loop keeps every register but a0 .. a5 (IOS_SUM_KEEP). *)
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AE2k AsanCells TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportCg TransportGRunA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import io_send_seg_cut.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.TransportG.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The addresses                                                       *)
(* ------------------------------------------------------------------ *)

(* The entry of the stretch, the loop's head, the store of the sum, and the join it goes on at. *)
Definition IOS_SUM_AT : Z := IOS_AT 0x2cc.
Definition IOS_SUM_HEAD : Z := IOS_AT 0x2d8.
Definition IOS_SUM_STORE : Z := IOS_AT 0x52c.
Definition IOS_SUM_JOIN : Z := IOS_AT 0x314.

Lemma ios_sum_addrs :
  transport_text + IOS_SUM_AT = 0x8302c /\ transport_text + IOS_SUM_HEAD = 0x83038 /\
  transport_text + IOS_SUM_STORE = 0x8328c /\ transport_text + IOS_SUM_JOIN = 0x83074.
Proof. repeat split; reflexivity. Qed.

(* The registers the stretch keeps: all but a0 .. a5 (x10 .. x15). *)
Definition IOS_SUM_KEEP : list (bv 5) :=
  [1%bv; 2%bv; 3%bv; 4%bv; 5%bv; 6%bv; 7%bv; 8%bv; 9%bv; 16%bv; 17%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv;
   23%bv; 24%bv; 25%bv; 26%bv; 27%bv; 28%bv; 29%bv; 30%bv; 31%bv].

Ltac su_kin := unfold IOS_SUM_KEEP; cbn [In]; repeat (first [left; reflexivity | right]).

(* ------------------------------------------------------------------ *)
(* The symbolic states                                                 *)
(* ------------------------------------------------------------------ *)

(* Atoms 0 .. 31 are the registers at the state's pc; s4 (atom 20) holds the shadow base of the token engine.
   su_ess   +0x2cc, no region;
   su_hss   +0x2d8, turn i: the body byte at a3 as atom 32 (read-only), a0 below 2 ^ 47 - 2, and the shadow entry
            su_SH of the one byte at a0;
   su_tss   +0x52c: the two bytes at sp + 80, writable (sp in [2 ^ 46, 2 ^ 47], the machine stack). *)
Definition su_Bx : sv := SOff 20 0.
Definition su_PHI : Z := 2 ^ 47 - 2.
Definition su_ess : sstate := mkSS IOS_SUM_AT sr_atoms [] None (mkFacts [] [] []).
Definition su_rg : YP09.region := YP09.mkRegion (Some 13%nat) 0 1 0 0 [YP09.mkChunk 0 (CVal 1 (SOff 32 0))].
Definition su_G : facts :=
  mkFacts [(20%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (10%nat, mkAF 0 su_PHI 0); (32%nat, mkAF 0 255 0)] [] [].
Definition su_hss : sstate := mkSS IOS_SUM_HEAD sr_atoms [su_rg] None su_G.
Definition su_SH : list shent := [mkSHE 10 0 1].
Definition su_trg : YP09.region := YP09.mkRegion (Some 2%nat) 80 82 80 82 [].
Definition su_tG : facts := mkFacts [(2%nat, mkAF (2 ^ 46) (2 ^ 47) 0)] [] [].
Definition su_tss : sstate := mkSS IOS_SUM_STORE sr_atoms [su_trg] None su_tG.

(* ------------------------------------------------------------------ *)
(* Bytes and the model's sum                                           *)
(* ------------------------------------------------------------------ *)

Lemma su_nth_bz : forall (l : list byte) j, nth j (map DSpec.bz l) 0 = DSpec.at8 l j.
Proof. intros l j. unfold DSpec.at8. rewrite <- (map_nth DSpec.bz l (DSpec.b8 0) j). reflexivity. Qed.

Lemma su_nth_skipn : forall (l : list byte) k i d, nth i (skipn k l) d = nth (k + i) l d.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l i d; [reflexivity|].
  destruct l as [|x l]; [destruct i; reflexivity | cbn [skipn]; rewrite IH; reflexivity].
Qed.

(* The running sum of the first i body bytes. *)
Definition su_sum (frame : list byte) (i : nat) : Z := DSpec.sum_bytes (firstn i (skipn 30 frame)).

Lemma su_sum_S : forall (frame : list byte) (i : nat), (30 + i < length frame)%nat ->
  su_sum frame (S i) = su_sum frame i + DSpec.at8 frame (30 + i).
Proof.
  intros frame i Hi. unfold su_sum. rewrite DSpec.sum_bytes_firstn_S by (rewrite length_skipn; lia).
  f_equal. unfold DSpec.at8. rewrite su_nth_skipn. reflexivity.
Qed.

Lemma su_sum_range : forall (frame : list byte) (i : nat), 0 <= su_sum frame i <= 255 * Z.of_nat i.
Proof.
  intros frame i. unfold su_sum. pose proof (DSpec.sum_bytes_range (firstn i (skipn 30 frame))) as H.
  rewrite length_firstn in H. lia.
Qed.

Lemma su_add_den : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  unfold bv_wrap. rewrite <- Zplus_mod. reflexivity.
Qed.

(* The body's bytes read: addressable, in application memory, below 2 ^ 47 - 1. *)
Lemma su_rd : forall (W : world tfibsegs) (mem : word -> option byte) (p len n : Z),
  decode_rd_ok W mem p len -> 0 <= n -> 30 + n <= len ->
  range_addressable (aview tfibsegs (w_H W) mem) SHADOW_OFF (p + 30) n /\
  (forall x, p + 30 <= x < p + 30 + n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) /\
  0 <= p /\ p + 30 + n <= su_PHI + 1.
Proof.
  intros W mem p len n (_ & Hra & _ & Ham & H0 & _) Hn Hl.
  unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Ham.
  split; [apply (range_addressable_sub _ _ p len); [exact Hra | lia | lia]|].
  split; [intros x Hx; unfold SHADOW_OFF; lia|].
  unfold su_PHI. lia.
Qed.

(* The awr obligation of a run over read-only regions. *)
Lemma su_awr_ro : forall E rs G XO OUT STK sp0 FP bl0 blc ly own,
  rs_read_only rs = true -> awr_ok_x E rs G XO OUT STK sp0 FP bl0 blc ly own.
Proof.
  intros E rs G XO OUT STK sp0 FP bl0 blc ly own Hro a (r & Hin & Hx).
  unfold rs_read_only in Hro. rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* Run helpers                                                         *)
(* ------------------------------------------------------------------ *)

(* The value of register r in the machine state of a symbolic state HS. *)
Ltac su_reg HS r v H tac :=
  lazymatch type of HS with
  | st_ok_pi ?segsx ?vl ?Ex ?ssx (restrict ?Hh ?msx) =>
      let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
      assert (H : YK11.getr (ms_regs msx) r = v) by
        (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* A read-only run kept the memory. *)
Ltac su_ro HF EM :=
  lazymatch type of HF with
  | frame_of ?E ?rs _ _ => pose proof (frame_of_read_only E rs _ _ ltac:(vm_compute; reflexivity) HF) as EM
  end.

(* The windows a run wrote, each closed by tac. *)
Ltac su_win Hin Hx tac :=
  lazymatch type of Hin with In ?x ?l => let l' := eval vm_compute in l in change (In x l') in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin | Hin]; [injection Hin as <- <- <-; cbn [base_val] in Hx; tac |]);
  destruct Hin.

(* Name the valuation of the state HS: in HS, its shadow entry SHOK and its img_env fact only. *)
Ltac su_setE HS SHOK En :=
  lazymatch type of HS with st_ok_pi _ _ ?EF _ _ =>
    lazymatch goal with H : img_env _ _ EF |- _ => set (En := EF) in HS, SHOK, H end end.

Section st. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).

(* The valuation of a fresh state: the 32 registers, then the extra atoms. *)
Definition su_E (r : bvmap 5 word) (extra : list word) : env := Eimg (PI := PI_transport) (Ereg r extra).

Lemma su_ew : forall r extra n (x : bv 5), Z.of_nat n = bv_unsigned x -> ew (su_E r extra) n = YK11.getr r x.
Proof. intros r extra n x Hn. unfold su_E. apply ew_Eimg_Ereg_nat. exact Hn. Qed.

Lemma su_ew32 : forall r b, ew (su_E r [w64 b]) 32 = w64 b.
Proof. intros r b. unfold su_E. rewrite Eimg_low by (unfold A_TEXT; lia). exact (ew_Ereg_extra r _ 0). Qed.

Lemma su_agree : forall r extra E, (forall m, (m < 1024)%nat -> ew E m = ew (su_E r extra) m) ->
  ed E = ed (su_E r extra) -> env_agree 32 (Ereg r extra) E.
Proof.
  intros r extra E H1 H2. split.
  - intros m Hm. rewrite (H1 m ltac:(lia)). unfold su_E. apply Eimg_low. unfold A_TEXT. lia.
  - rewrite H2. reflexivity.
Qed.

(* +0x2cc: no region. *)
Lemma su_start_ok : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte),
  st_ok_pi segs VAL (su_E r []) su_ess
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + IOS_SUM_AT)) mem (YK11.seg_rom segs))).
Proof.
  intros W r mem. rewrite restrict_mkst_fx. unfold su_ess.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - unfold su_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_nil.
  - exact I.
  - exact (conj I (conj I I)).
Qed.

(* +0x2d8, turn i: the body byte at a3 = q as atom 32; a0 = q. *)
Lemma su_head_ok : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (q b : Z),
  YK11.getr r 10 = w64 q -> YK11.getr r 13 = w64 q -> YK11.getr r 20 = w64 SHADOW_OFF ->
  0 <= q <= su_PHI -> 0 <= b < 256 -> val_mem segs (mrestrict (w_H W) mem) q 1 b ->
  st_ok_pi segs VAL (su_E r [w64 b]) su_hss
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + IOS_SUM_HEAD)) mem (YK11.seg_rom segs))).
Proof.
  intros W r mem q b R10 R13 R20 Hq Hb V.
  unfold su_PHI in Hq.
  assert (U10 : bv_unsigned (ew (su_E r [w64 b]) 10) = q)
    by (rewrite (su_ew r _ 10 10%bv eq_refl), R10; unfold w64; apply unsigned_lit_small; lia).
  assert (U13 : bv_unsigned (ew (su_E r [w64 b]) 13) = q)
    by (rewrite (su_ew r _ 13 13%bv eq_refl), R13; unfold w64; apply unsigned_lit_small; lia).
  assert (U20 : bv_unsigned (ew (su_E r [w64 b]) 20) = SHADOW_OFF)
    by (rewrite (su_ew r _ 20 20%bv eq_refl), R20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
  assert (U32 : bv_unsigned (ew (su_E r [w64 b]) 32) = b)
    by (rewrite su_ew32; unfold w64; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold su_hss.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - unfold su_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold su_rg, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U13.
    split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val segs _ _ q 0 1 (SOff 32 0) b).
    + cbn [sv_denot]. rewrite su_ew32, Z.add_0_r. unfold w64. rewrite unsigned_lit_small by lia. reflexivity.
    + cbn. lia.
    + cbn. lia.
    + rewrite Z.add_0_r. exact V.
  - exact (conj I I).
  - unfold facts_ok, su_G. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U20, U10, U32. rewrite !Z.pow_0_r, !Z.mod_1_r.
    unfold SHADOW_OFF, su_PHI. repeat split; try exact I; lia.
Qed.

(* +0x52c: the two bytes at sp + 80 the store writes (writable: bytes of the journal's window). *)
Lemma su_tail_ok : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) (sp : Z),
  YK11.getr r 2 = w64 sp -> 2 ^ 46 <= sp -> sp + 82 <= 2 ^ 47 ->
  (forall a, sp + 80 <= a < sp + 82 -> apresent (w_H W) mem a) ->
  st_ok_pi segs VAL (su_E r []) su_tss
    (restrict (w_H W) (@YK11.mkst fx r (Z_to_bv 64 (BASE + IOS_SUM_STORE)) mem (YK11.seg_rom segs))).
Proof.
  intros W r mem sp R2 H0 H1 Hp.
  assert (U2 : bv_unsigned (ew (su_E r []) 2) = sp)
    by (rewrite (su_ew r _ 2 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
  rewrite restrict_mkst_fx. unfold su_tss.
  apply (@pa_entry_st_ok_full fx rc transport_listing PI_transport).
  - unfold su_E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - apply Forall_cons; [|apply Forall_nil]. unfold su_trg, YP09.region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val]. rewrite U2.
    split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
    intros o Ho. apply (apresent_writable segs). apply Hp. lia.
  - exact (conj I I).
  - unfold facts_ok, su_tG. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite U2. rewrite !Z.pow_0_r, !Z.mod_1_r.
    repeat split; try exact I; lia.
Qed.

(* The shadow entry of turn i: the byte at a0 = q inside the addressable range [a, a + n). *)
Lemma su_shok : forall (W : world segs) (r : bvmap 5 word) (mem : word -> option byte) extra (q a n : Z),
  YK11.getr r 10 = w64 q -> YK11.getr r 20 = w64 SHADOW_OFF -> 0 <= q < 2 ^ 64 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF a n -> a <= q -> q + 1 <= a + n ->
  (forall x, a <= x < a + n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  sh_ok segs su_Bx su_SH (su_E r extra) (mrestrict (w_H W) mem).
Proof.
  intros W r mem extra q a n R10 R20 Hq HRA H1 H2 Happ.
  apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem (su_E r extra) su_Bx 10%nat a n q 0 1).
  - exact HRA.
  - unfold su_Bx. apply U_atom; [|unfold SHADOW_OFF; lia]. rewrite (su_ew r _ 20 20%bv eq_refl). exact R20.
  - apply U_atom; [|lia]. rewrite (su_ew r _ 10 10%bv eq_refl). exact R10.
  - lia.
  - lia.
  - intros x Hx. cbn [Z.min Z.max] in Hx. apply Happ. lia.
Qed.

End st.

(* ------------------------------------------------------------------ *)
(* The loop                                                            *)
(* ------------------------------------------------------------------ *)

Section loop. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HGX : gx_ok segs B TG.G_HARNESS.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sj : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (k : Z).
(* The memory at +0x2cc; the loop writes none. *)
Variable mem : word -> option byte.
(* The registers at +0x2cc, the frame at p, the body length n. *)
Variables (regs : bvmap 5 word) (p : Z) (frame : list byte) (n : nat).
Variable Q : world segs -> config -> Prop.
Hypothesis Hn : (30 + n <= length frame)%nat.
Hypothesis HG8 : garr8 segs (mrestrict (w_H W) mem) p (map DSpec.bz frame).
Hypothesis HRA : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (p + 30) (Z.of_nat n).
Hypothesis HAPP : forall x, p + 30 <= x < p + 30 + Z.of_nat n -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416).
Hypothesis Hp : 0 <= p /\ p + 30 + Z.of_nat n <= su_PHI + 1.
Hypothesis HR20 : YK11.getr regs 20 = w64 SHADOW_OFF.

Local Abbreviation su_J md :=
  (@W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W mem md k).
Local Abbreviation su_at pc r md :=
  (mkCfg (@YK11.mkst fx r (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs)) md).

(* What the loop leaves at +0x52c: a1 = the sum of the n body bytes, the other registers but a0 .. a5 kept. *)
Hypothesis HEXIT : forall (r : bvmap 5 word) (md : Model), su_J md ->
  YK11.getr r 11 = w64 (su_sum frame n) -> (forall x, In x IOS_SUM_KEEP -> YK11.getr r x = YK11.getr regs x) ->
  SRr segs W (su_at IOS_SUM_STORE r md) Q.

(* The registers at +0x2d8 before turn i. *)
Definition su_inv (r : bvmap 5 word) (i : nat) : Prop :=
  YK11.getr r 10 = w64 (p + 30 + Z.of_nat i) /\ YK11.getr r 13 = w64 (p + 30 + Z.of_nat i) /\
  YK11.getr r 12 = w64 (Z.of_nat n - Z.of_nat i) /\ YK11.getr r 11 = w64 (su_sum frame i) /\
  (forall x, In x IOS_SUM_KEEP -> YK11.getr r x = YK11.getr regs x).

(* What the next turn gives. *)
Definition su_K (i : nat) : Prop :=
  forall (r : bvmap 5 word) (md : Model), (S i < n)%nat -> su_inv r (S i) -> su_J md ->
    SRr segs W (su_at IOS_SUM_HEAD r md) Q.

(* +0x2d8 .. +0x2fc, turn i: the instrumented check of the byte at a0 = p + 30 + i (the token engine decides it
   from the shadow entry su_SH, so the error path at +0x30c is not reached), the load of p[30 + i] at a3, a1 + it,
   a0, a3 one up, a2 one down; `bnez a2` back to +0x2d8, else `j` to +0x52c. *)
Lemma ios_sum_turn : forall (i : nat) (r : bvmap 5 word) (md : Model),
  (i < n)%nat -> su_inv r i -> su_J md -> su_K i -> SRr segs W (su_at IOS_SUM_HEAD r md) Q.
Proof.
  intros i r md Hi Hinv HJ HK.
  pose proof Hinv as (R10 & R13 & R12 & R11 & RK).
  assert (R20 : YK11.getr r 20 = w64 SHADOW_OFF) by (rewrite RK by su_kin; exact HR20).
  pose proof Hp as [Hp0 Hp1]. unfold su_PHI in Hp1.
  assert (Hj : (30 + i < length (map DSpec.bz frame))%nat) by (rewrite length_map; lia).
  destruct (HG8 (30 + i)%nat Hj) as [Vb Bb]. rewrite su_nth_bz in Vb, Bb.
  replace (p + Z.of_nat (30 + i)) with (p + 30 + Z.of_nat i) in Vb by lia.
  remember (DSpec.at8 frame (30 + i)%nat) as b eqn:Eb.
  pose proof (su_head_ok W r mem (p + 30 + Z.of_nat i) b R10 R13 R20 ltac:(unfold su_PHI; lia) Bb Vb) as HS.
  pose proof (su_shok W r mem [w64 b] (p + 30 + Z.of_nat i) (p + 30) (Z.of_nat n) R10 R20 ltac:(lia) HRA
    ltac:(lia) ltac:(lia) HAPP) as SHOK.
  pose proof (su_sum_range frame i) as Hs.
  set (E0 := su_E r [w64 b]) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, su_E; apply Eimg_env).
  assert (X10 : ew E0 10 = w64 (p + 30 + Z.of_nat i)) by (unfold E0; rewrite (su_ew r _ 10 10%bv eq_refl); exact R10).
  assert (X13 : ew E0 13 = w64 (p + 30 + Z.of_nat i)) by (unfold E0; rewrite (su_ew r _ 13 13%bv eq_refl); exact R13).
  assert (X12 : ew E0 12 = w64 (Z.of_nat n - Z.of_nat i))
    by (unfold E0; rewrite (su_ew r _ 12 12%bv eq_refl); exact R12).
  assert (X11 : ew E0 11 = w64 (su_sum frame i)) by (unfold E0; rewrite (su_ew r _ 11 11%bv eq_refl); exact R11).
  assert (X32 : ew E0 32 = w64 b) by (unfold E0; apply su_ew32).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
    0 []) as RUNTO.
  pose proof (paj_branch (PI := PI_transport)) as BR.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { apply su_awr_ro. vm_compute. reflexivity. }
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
  rename ms into ms1.
  su_ro HF EM1. clear HF HFr HG.
  su_setE HS SHOK E1.
  assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
    by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a2 - 1 <> 0: turn i + 1 *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom_off E1 12 (Z.of_nat n - Z.of_nat i) (-1) ltac:(rewrite HE1 by lia; exact X12) ltac:(lia)
      ltac:(lia)), U_lit in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_SUM_HEAD.
    { apply su_awr_ro. vm_compute. reflexivity. }
    set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
    rename ms into ms2.
    su_ro HF EM2. clear HF HFr HG.
    su_setE HS SHOK E2.
    assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
      by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
    su_reg HS (10%bv : bv 5) (w64 (p + 30 + Z.of_nat (S i))) Q10
      ltac:(cbn [sv_denot]; rewrite (HE2 10%nat) by lia; rewrite X10; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia).
    su_reg HS (13%bv : bv 5) (w64 (p + 30 + Z.of_nat (S i))) Q13
      ltac:(cbn [sv_denot]; rewrite (HE2 13%nat) by lia; rewrite X13; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia).
    su_reg HS (12%bv : bv 5) (w64 (Z.of_nat n - Z.of_nat (S i))) Q12
      ltac:(cbn [sv_denot]; rewrite (HE2 12%nat) by lia; rewrite X12; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia).
    su_reg HS (11%bv : bv 5) (w64 (su_sum frame (S i))) Q11
      ltac:(cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; rewrite (HE2 11%nat), (HE2 32%nat) by lia;
            rewrite X11, X32; unfold w64; rewrite su_add_den; f_equal; rewrite (su_sum_S frame i) by lia;
            rewrite Eb; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?SF (restrict _ _) =>
      pose proof (regs_kept_of_st_ok_pi E2 SF _ r [w64 b] IOS_SUM_KEEP HS
        (su_agree r [w64 b] E2 HE2 eq_refl) ltac:(vm_compute; reflexivity)) as KR end.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite EM2, EM1 in HJ |- *.
    apply HK; [lia | | exact HJ].
    split; [exact Q10|]. split; [exact Q13|]. split; [exact Q12|]. split; [exact Q11|].
    intros x Hx. rewrite (KR x Hx). exact (RK x Hx).
  - (* a2 - 1 = 0: the loop ends, a1 = the sum of the n bytes *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom_off E1 12 (Z.of_nat n - Z.of_nat i) (-1) ltac:(rewrite HE1 by lia; exact X12) ltac:(lia)
      ltac:(lia)), U_lit in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc.
    assert (EI : S i = n) by lia.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_SUM_STORE.
    { apply su_awr_ro. vm_compute. reflexivity. }
    set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
    rename ms into ms2.
    su_ro HF EM2. clear HF HFr HG.
    su_setE HS SHOK E2.
    assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
      by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
    su_reg HS (11%bv : bv 5) (w64 (su_sum frame n)) Q11
      ltac:(cbn [sv_denot]; rewrite !Z.add_0_r, !Z_to_bv_bv_unsigned; rewrite (HE2 11%nat), (HE2 32%nat) by lia;
            rewrite X11, X32; unfold w64; rewrite su_add_den; f_equal; rewrite <- EI;
            rewrite (su_sum_S frame i) by lia; rewrite Eb; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?SF (restrict _ _) =>
      pose proof (regs_kept_of_st_ok_pi E2 SF _ r [w64 b] IOS_SUM_KEEP HS
        (su_agree r [w64 b] E2 HE2 eq_refl) ltac:(vm_compute; reflexivity)) as KR end.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite EM2, EM1 in HJ |- *.
    apply HEXIT; [exact HJ | exact Q11 |].
    intros x Hx. rewrite (KR x Hx). exact (RK x Hx).
Qed.

(* The turns from i on, by induction on the turns left. *)
Lemma ios_sum_iter : forall (m i : nat) (r : bvmap 5 word) (md : Model),
  m = (n - i)%nat -> (i < n)%nat -> su_inv r i -> su_J md -> SRr segs W (su_at IOS_SUM_HEAD r md) Q.
Proof.
  induction m as [|m IH]; intros i r md Hm Hi Hinv HJ; [lia|].
  apply (ios_sum_turn i r md Hi Hinv HJ). unfold su_K.
  intros r1 md1 Hi1 Hinv1 HJ1. exact (IH (S i) r1 md1 ltac:(lia) Hi1 Hinv1 HJ1).
Qed.

Hypothesis HR9 : YK11.getr regs 9 = w64 p.
Hypothesis HR12 : YK11.getr regs 12 = w64 (Z.of_nat n).
Hypothesis HR13 : YK11.getr regs 13 = w64 (p + 30).

(* +0x2cc .. +0x2d4: a1 = 0; `beqz a2` (a2 = n) to +0x52c with a1 = 0 = the sum of no byte; else a0 = s1 + 30 and
   the turns from i = 0 with the sum 0. *)
Lemma ios_sum_loop : forall (md : Model), su_J md -> SRr segs W (su_at IOS_SUM_AT regs md) Q.
Proof.
  intros md HJ.
  pose proof Hp as [Hp0 Hp1]. unfold su_PHI in Hp1.
  pose proof (su_start_ok W regs mem) as HS.
  assert (SHOK : sh_ok segs su_Bx [] (su_E regs []) (mrestrict (w_H W) mem)) by apply Forall_nil.
  set (E0 := su_E regs []) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, su_E; apply Eimg_env).
  assert (X9 : ew E0 9 = w64 p) by (unfold E0; rewrite (su_ew regs _ 9 9%bv eq_refl); exact HR9).
  assert (X12 : ew E0 12 = w64 (Z.of_nat n)) by (unfold E0; rewrite (su_ew regs _ 12 12%bv eq_refl); exact HR12).
  assert (X13 : ew E0 13 = w64 (p + 30)) by (unfold E0; rewrite (su_ew regs _ 13 13%bv eq_refl); exact HR13).
  pose proof (@paj_run_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX 0 [])
    as RUN.
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
    0 []) as RUNTO.
  pose proof (paj_branch (PI := PI_transport)) as BR.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { apply su_awr_ro. vm_compute. reflexivity. }
  set (md1 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md1. clear mat.
  rename ms into ms1.
  su_ro HF EM1. clear HF HFr HG.
  su_setE HS SHOK E1.
  assert (HE1 : forall m, (m < 1024)%nat -> ew E1 m = ew E0 m)
    by (intros m Hm; unfold E1; repeat rewrite ew_ewset_other by lia; reflexivity).
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  - (* a2 = 0: n = 0, to +0x52c *)
    rewrite branch_eq_U in Hc.
    rewrite (U_atom E1 12 (Z.of_nat n) ltac:(rewrite HE1 by lia; exact X12) ltac:(lia)), U_lit in Hc by lia.
    apply Z.eqb_eq in Hc.
    assert (EN : n = 0%nat) by lia.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_SUM_STORE.
    { apply su_awr_ro. vm_compute. reflexivity. }
    set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
    rename ms into ms2.
    su_ro HF EM2. clear HF HFr HG.
    su_setE HS SHOK E2.
    assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
      by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
    su_reg HS (11%bv : bv 5) (w64 (su_sum frame n)) Q11
      ltac:(cbn [sv_denot]; unfold su_sum; rewrite EN; reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?SF (restrict _ _) =>
      pose proof (regs_kept_of_st_ok_pi E2 SF _ regs [] IOS_SUM_KEEP HS
        (su_agree regs [] E2 HE2 eq_refl) ltac:(vm_compute; reflexivity)) as KR end.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite EM2, EM1 in HJ |- *.
    apply HEXIT; [exact HJ | exact Q11 | exact KR].
  - (* a2 <> 0: a0 = p + 30, to +0x2d8 and turn 0 *)
    rewrite branch_eq_U in Hc.
    rewrite (U_atom E1 12 (Z.of_nat n) ltac:(rewrite HE1 by lia; exact X12) ltac:(lia)), U_lit in Hc by lia.
    apply Z.eqb_neq in Hc.
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_SUM_HEAD.
    { apply su_awr_ro. vm_compute. reflexivity. }
    set (md2 := with_vm_backing (m_vm_lazy md1) mat md1) in *. clearbody md2. clear mat.
    rename ms into ms2.
    su_ro HF EM2. clear HF HFr HG.
    su_setE HS SHOK E2.
    assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
      by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; apply HE1; exact Hm).
    su_reg HS (10%bv : bv 5) (w64 (p + 30 + Z.of_nat 0)) Q10
      ltac:(cbn [sv_denot]; rewrite (HE2 9%nat) by lia; rewrite X9; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia).
    su_reg HS (13%bv : bv 5) (w64 (p + 30 + Z.of_nat 0)) Q13
      ltac:(cbn [sv_denot]; rewrite (HE2 13%nat) by lia; rewrite X13; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia).
    su_reg HS (12%bv : bv 5) (w64 (Z.of_nat n - Z.of_nat 0)) Q12
      ltac:(cbn [sv_denot]; rewrite (HE2 12%nat) by lia; rewrite X12; unfold w64;
            rewrite unsigned_lit_small by lia; f_equal; lia).
    su_reg HS (11%bv : bv 5) (w64 (su_sum frame 0)) Q11 ltac:(reflexivity).
    lazymatch type of HS with st_ok_pi _ _ _ ?SF (restrict _ _) =>
      pose proof (regs_kept_of_st_ok_pi E2 SF _ regs [] IOS_SUM_KEEP HS
        (su_agree regs [] E2 HE2 eq_refl) ltac:(vm_compute; reflexivity)) as KR end.
    cbn [ms_regs restrict] in KR.
    pmkst HS. rewrite EM2, EM1 in HJ |- *.
    apply (ios_sum_iter (n - 0) 0 _ _ eq_refl); [lia | | exact HJ].
    split; [exact Q10|]. split; [exact Q13|]. split; [exact Q12|]. split; [exact Q11 | exact KR].
Qed.

End loop.

(* ------------------------------------------------------------------ *)
(* The store of the sum                                                *)
(* ------------------------------------------------------------------ *)

Section tail. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transport_listing PI_transport).
Local Abbreviation BASE := (@pa_val _ transport_listing PI_transport A_TEXT).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.
Hypothesis HGX : gx_ok segs B TG.G_HARNESS.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (Sj : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (k : Z).
Variable mem : word -> option byte.
Variable Q : world segs -> config -> Prop.

Local Abbreviation su_J m md :=
  (@W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS 0 [] STK sp0 FP ly Sj W0 mem0 md0 own lyc Sc W m md k).

(* +0x52c .. +0x534: a0 = 0, the 2-byte store of a1 at sp + 80 (f + 72, the struct's body_sum), `j` to +0x314. The
   store is a byte of io_send's own stack window, which the journal's window [sp0 - STK, sp0) holds (awr_byte). *)
Lemma ios_sum_tail : forall (r : bvmap 5 word) (md : Model) (s sp : Z),
  su_J mem md -> YK11.getr r 11 = w64 s -> YK11.getr r 2 = w64 sp -> 0 <= s < 2 ^ 64 ->
  sp0 - STK <= sp + 80 -> sp + 82 <= sp0 ->
  (forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
     su_J mem2 md2 -> YK11.getr regs2 10 = w64 0 ->
     (forall x, In x IOS_SUM_KEEP -> YK11.getr regs2 x = YK11.getr r x) ->
     val_mem segs (mrestrict (w_H W) mem2) (sp + 80) 2 (s mod 2 ^ 16) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 80 <= a < sp + 82) -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
     SRr segs W (mkCfg (@YK11.mkst fx regs2 (Z_to_bv 64 (BASE + IOS_SUM_JOIN)) mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W (mkCfg (@YK11.mkst fx r (Z_to_bv 64 (BASE + IOS_SUM_STORE)) mem (YK11.seg_rom segs)) md) Q.
Proof.
  intros r md s sp HJ R11 R2 Hs Hsp1 Hsp2 HK.
  pose proof HJ as (HSTK & _ & (memS & HJi & _) & _).
  rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & Hstk & _).
  pose proof Hstk as (Hsp0a & Hstk0 & Hceil & Hslo & Hshi & H47 & _).
  clear HJi memS.
  pose proof asan_consts as (C1 & _).
  assert (Hsp : 2 ^ 46 <= sp /\ sp + 82 <= 2 ^ 47) by lia.
  pose proof (su_tail_ok W r mem sp R2 ltac:(lia) ltac:(lia) ltac:(intros a Ha; apply Hpres; lia)) as HS.
  assert (SHOK : sh_ok segs su_Bx [] (su_E r []) (mrestrict (w_H W) mem)) by apply Forall_nil.
  set (E0 := su_E r []) in HS, SHOK.
  assert (HEI : img_env VAL A_LIM E0) by (unfold E0, su_E; apply Eimg_env).
  assert (Usp : bv_unsigned (ew E0 2) = sp)
    by (unfold E0; rewrite (su_ew r _ 2 2%bv eq_refl), R2; unfold w64; apply unsigned_lit_small; lia).
  assert (X11 : ew E0 11 = w64 s) by (unfold E0; rewrite (su_ew r _ 11 11%bv eq_refl); exact R11).
  pose proof (@paj_run_to_x fx rc tfib_sink_head transport_listing PL_transport PI_transport B LAWS TG.G_HARNESS HGX
    0 []) as RUNTO.
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan IOS_SUM_JOIN.
  { lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
      let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end.
    apply awr_ok_x_cons; [|apply awr_ok_x_nil].
    intros a Ha. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. rewrite Usp in Ha.
    left. split; [unfold awr_byte; left; lia | lia]. }
  set (md2 := with_vm_backing (m_vm_lazy md) mat md) in *. clearbody md2. clear mat.
  rename ms into ms2.
  su_setE HS SHOK E2.
  assert (HE2 : forall m, (m < 1024)%nat -> ew E2 m = ew E0 m)
    by (intros m Hm; unfold E2; repeat rewrite ew_ewset_other by lia; reflexivity).
  (* the view kept outside [sp + 80, sp + 82) *)
  assert (KV : forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 80 <= a < sp + 82) ->
    aview segs (w_H W) (ms_mem ms2) a = aview segs (w_H W) mem a).
  { intros a Ha H1.
    apply (kept_of_frame _ _ _ _ _ (fun x => sp + 80 <= x < sp + 82) HFr); [| exact Ha | exact H1].
    intros b wlo whi x Hin Hx. cbv beta.
    su_win Hin Hx ltac:(rewrite ?Usp in Hx; lia). }
  assert (GA : forall a, apresent (w_H W) mem a -> apresent (w_H W) (ms_mem ms2) a)
    by (intros a Ha; exact (apresent_grows _ _ _ a HG Ha)).
  clear HF HFr HG.
  (* the two bytes stored *)
  pose proof (st_ok_pi_region_nth E2 _ (restrict (w_H W) ms2) 0 _ HS eq_refl) as RG. cbn [ms_mem restrict] in RG.
  destruct RG as (_ & _ & _ & HCH). apply Forall_inv in HCH.
  pose proof (val_of_chunk_any segs E2 _ _ _ _ _ HCH ltac:(lia)) as VS.
  cbn [YP09.r_base base_val] in VS. rewrite (HE2 2%nat) in VS by lia. rewrite Usp in VS.
  replace (bv_unsigned (sv_denot E2 (SOff 11 0)) mod 2 ^ (8 * Z.of_N 2)) with (s mod 2 ^ 16) in VS
    by (cbn [sv_denot]; rewrite (HE2 11%nat) by lia; rewrite X11; unfold w64;
        rewrite Z.add_0_r, Z_to_bv_bv_unsigned, unsigned_lit_small by lia; reflexivity).
  su_reg HS (10%bv : bv 5) (w64 0) Q10 ltac:(reflexivity).
  lazymatch type of HS with st_ok_pi _ _ _ ?SF (restrict _ _) =>
    pose proof (regs_kept_of_st_ok_pi E2 SF _ r [] IOS_SUM_KEEP HS
      (su_agree r [] E2 HE2 eq_refl) ltac:(vm_compute; reflexivity)) as KR end.
  cbn [ms_regs restrict] in KR.
  pmkst HS.
  apply HK; [exact HJ | exact Q10 | exact KR | exact VS | exact KV | exact GA].
Qed.

End tail.

(* ------------------------------------------------------------------ *)
(* The stretch +0x2cc .. +0x534                                        *)
(* ------------------------------------------------------------------ *)

(* At +0x2cc (0x8302c) io_send holds the parse's registers: sp, s1 = p, a2 = body_len = numbytes - 16, a3 = p + 30,
   s4 = the shadow base. The stretch sums the body bytes p[30 .. 30 + body_len) with checked 1-byte loads (no error
   path: every byte lies in the frame, whose bytes decode_rd_ok marks addressable), stores the low 16 bits of the sum
   at sp + 80 (f + 72, the struct's body_sum: fuzz_frame's fr_body_sum of the bytes) and goes on at +0x314 (0x83074)
   with a0 = 0. It writes no other byte and keeps every register but a0 .. a5. *)
Lemma ios_sum_seg : forall (fx : YK11.FPState) (rc : YM05.RunCeil) (B : asyms) (STK sp0 : Z) (FP : list (Z * Z))
    (ly : alayout) (S : astate) (W0 : world tfibsegs) (mem0 : word -> option byte) (md0 : Model)
    (own : list (Z * Z)) (lyc : alayout) (Sc : astate) (W : world tfibsegs) (mem : word -> option byte)
    (md : Model) (k : Z) (regs : bvmap 5 word) (sp p : Z) (frame : list byte)
    (Q : world tfibsegs -> config -> Prop),
  AR_laws tfibsegs B -> gx_ok tfibsegs B TG.G_HARNESS ->
  @W_journalG.ajournal_gx rc AE2k.tfib_sink_head tfibsegs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
    lyc Sc W mem md k ->
  YK11.getr regs 2 = w64 sp -> YK11.getr regs 9 = w64 p -> YK11.getr regs 12 = w64 (DSpec.fr_body_len frame) ->
  YK11.getr regs 13 = w64 (p + 30) -> YK11.getr regs 20 = w64 SHADOW_OFF ->
  sp0 - STK <= sp + 80 -> sp + 82 <= sp0 ->
  garr8 tfibsegs (mrestrict (w_H W) mem) p (map DSpec.bz frame) ->
  decode_rd_ok W mem p (Z.of_nat (length frame)) ->
  16 <= DSpec.fr_numbytes frame -> DSpec.fr_numbytes frame <= Z.of_nat (length frame) - 14 ->
  (forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
     @W_journalG.ajournal_gx rc AE2k.tfib_sink_head tfibsegs B TG.G_HARNESS 0 [] STK sp0 FP ly S W0 mem0 md0 own
       lyc Sc W mem2 md2 k ->
     YK11.getr regs2 10 = w64 0 ->
     (forall x, In x IOS_SUM_KEEP -> YK11.getr regs2 x = YK11.getr regs x) ->
     val_mem tfibsegs (mrestrict (w_H W) mem2) (sp + 80) 2 (DSpec.fr_body_sum frame) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 80 <= a < sp + 82) ->
        aview tfibsegs (w_H W) mem2 a = aview tfibsegs (w_H W) mem a) ->
     (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
     SRr tfibsegs W (@cfg_at fx tfibsegs (transport_text + IOS_AT 0x314) regs2 mem2 md2) Q) ->
  SRr tfibsegs W (@cfg_at fx tfibsegs (transport_text + IOS_AT 0x2cc) regs mem md) Q.
Proof.
  intros fx rc B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W mem md k regs sp p frame Q
    LAWS HGX HJ R2 R9 R12 R13 R20 Hsp1 Hsp2 HG8 HRD HNB1 HNB2 HK.
  set (n := Z.to_nat (DSpec.fr_body_len frame)).
  assert (En : Z.of_nat n = DSpec.fr_body_len frame) by (unfold n, DSpec.fr_body_len; lia).
  assert (Hn : (30 + n <= length frame)%nat) by (unfold n, DSpec.fr_body_len; lia).
  destruct (su_rd W mem p (Z.of_nat (length frame)) (Z.of_nat n) HRD ltac:(lia) ltac:(lia)) as (HRA & HAPP & Hp).
  assert (EBS : DSpec.fr_body_sum frame = su_sum frame n mod 2 ^ 16) by reflexivity.
  rewrite <- En in R12.
  unfold cfg_at.
  change (SRr tfibsegs W (mkCfg (@YK11.mkst fx regs (Z_to_bv 64 (@pa_val _ transport_listing PI_transport A_TEXT
    + IOS_SUM_AT)) mem (YK11.seg_rom tfibsegs)) md) Q).
  refine (ios_sum_loop B LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k mem regs p frame n Q Hn HG8 HRA HAPP Hp
    R20 _ R9 R12 R13 md HJ).
  intros r md1 HJ1 R11 RK.
  apply (ios_sum_tail B LAWS HGX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W k mem Q r md1 (su_sum frame n) sp HJ1 R11
    ltac:(rewrite RK by su_kin; exact R2) ltac:(pose proof (su_sum_range frame n); unfold su_PHI in Hp; lia)
    Hsp1 Hsp2).
  intros regs2 mem2 md2 HJ2 Q10 RK2 VS KV GA.
  rewrite <- EBS in VS.
  exact (HK regs2 mem2 md2 HJ2 Q10 ltac:(intros x Hx; rewrite (RK2 x Hx); exact (RK x Hx)) VS KV GA).
Qed.
