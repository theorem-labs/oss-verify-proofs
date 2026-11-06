(* desk_named_cgW: the caller-journal walk of desk_named in image B (fuzz_transport.asan-ubsan, 0x85100 =
   transportb_sigma TB_desk_named, 53 words), and the theorem of lib/B/Prog/desk_named_cg.v.

   The machine part (module DNRun) is three footprint runs (lib/Lib/ExecF.v evtF, StepF's step), cut at the two calls
   of the bcmp wrapper (0x42d34 = transportb_sigma TB___interceptor_trampoline_bcmp):
     dn_run1_F  the entry 0x85100 to the first call (0x85184, return address 0x85188) or to the `ret` with a0 = 0:
                the 16-byte frame (ra at sp - 8, s0 at sp - 16); the UBSan pointer checks of p (p = 0 at 0x8510c,
                p >= 2^64 - 24 at 0x85110 - 0x85114), not taken as 0 < p and p + length body <= 2^63; the shadow
                base through GOT_CELL_K and CELL_K; the strz scan of the 9 bytes at p + 24 (s0), i counted up from
                0 in a1, each byte load after the UBSan check ~s0 < i (0x85134, not taken: s0 + i < 2^63) and after
                its instrumented check (the shadow byte is 0, or above the byte's offset in its granule, so the
                report call at 0x85168 is never reached). A NUL at index 8 reaches the call; any other length
                reaches `li a0,0` at 0x851a4 and the epilogue 0x851a8-0x851b4. The trap word 0x851d0 is never
                reached;
     dn_run2_F  the first call's return 0x85188: a0 = 0 gives a0 = SPEC_C24 (0x851b8) and the epilogue, else the
                second call (0x8519c, return address 0x851a0);
     dn_run3_F  the second call's return 0x851a0: a0 = 0 gives a0 = SPEC_PC (0x851c4), else a0 = 0 (0x851a4), and
                the epilogue.
   The functional content is the plain walk lib/Prog/T/desk_named.v and the UBSan twin lib/U/Prog/T/desk_named.v at
   image B's addresses; their pure lemmas are restated here (those files Require lib/TModel/TWorldMem.v, which
   redefines the load tactics).

   The walk (dn_holds) carries each run into SRr with lib/B/Prog/TransportFevt.v decode_run over an inner journal at
   the entry state (YCbq.v ajournal_sub_init, stack window [sp - DNAMED_STK, sp)), re-established across each run by
   YCbq.v ajournal_exec (a run writes only its 16-byte frame, dn_journal_run). Each bcmp call is YCbq.v aj_bcmp_at at
   the statement's abcmp_realizes (dn_bcmp). Its ranges: [p + 24, p + 32), a sub-range of the body, whose facts come
   from trans_src_ok through DgnTransportBCg.v trans_src_ok_rd; and TRANS_STR_C24 / TRANS_STR_PC (8 bytes), visible
   through trans_rom_view_rd, with their shadow from transport_cells and trans_dnamed_cells: on image B the two
   strings lie in two aligned groups of 8 shadow bytes (dn_str_rd). Each of those bytes and shadow bytes lies outside
   the frame and outside each call's window, so its view is kept (dn_rd_keep). bcmp's answer is 0 exactly when the
   two views agree; the views are the body's bytes (garr8) and the image's strings, so the three answers are
   desk_named_m's cases (dn_cmp, dn_r_c24, dn_r_pc, dn_r_none). The close composes the inner journal with the
   caller's (lib/B/Prog/YC85.v ajournal_sub_tok) and takes the kept bytes from YCbq.v acall_kept_of_journal
   (dn_close).
   The statement's trans_ro_rd_unowned and trans_rom_no_errno are not used: the strings are read from the entry
   state's trans_rom_view_rd, and their views are carried through the walk's own runs and calls. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require
  PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge ExecF StepF Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Img0 AsanCells.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require AsanKA AsanKAProof.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require DgnTransportBCg.
Import ListNotations.
Open Scope Z_scope.

(* ======== the machine runs ======== *)

Module DNRun.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.PropExec.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.MState.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Mem.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Exec.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Frame.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Cells.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Step.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Tac.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.Bytes.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ZBridge.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Img0.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKAProof.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.ExecF.
Import OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib.StepF.
Local Open Scope Z_scope.

(* The entry, the trampoline and the two return addresses: the listing's names and offsets from the entry
   (DgnTransportBList.v, the 53 slots of TB_desk_named). *)
Definition DN_ENTRY : Z := DgnTransportBAddr.transportb_sigma DgnTransportBSyms.TB_desk_named.
Definition DN_AT (off : Z) : Z := DN_ENTRY + off.
Definition DN_BCMP : Z := DgnTransportBAddr.transportb_sigma DgnTransportBSyms.TB___interceptor_trampoline_bcmp.
Definition DN_RET1 : Z := DN_AT 0x88.   (* 0x85188, after the jal at 0x85184 *)
Definition DN_RET2 : Z := DN_AT 0xa0.   (* 0x851a0, after the jal at 0x8519c *)

(* The start pc of a run is a name; StepF's step reads a literal. *)
Ltac dn_pc := lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      let v := eval vm_compute in pc in change pc with v
  end.

(* ---- spec_strz_len over the name field (lib/Prog/T/desk_named.v:39-57, at nth) ---- *)

Lemma dn_nz_le : forall l, (DgnSpec.nz_run l <= length l)%nat.
Proof. induction l as [|x l IH]; cbn; [lia|]. destruct (DgnSpec.bz x =? 0); lia. Qed.

Lemma dn_nz_lt : forall (l : list byte) j, (j < DgnSpec.nz_run l)%nat ->
  DgnSpec.bz (nth j l (Z_to_bv 8 0)) <> 0.
Proof.
  induction l as [|x l IH]; cbn; [intros; lia|].
  destruct (DgnSpec.bz x =? 0) eqn:E; intros j H; [lia|].
  destruct j as [|j]; cbn [nth].
  - apply Z.eqb_neq. exact E.
  - apply IH. lia.
Qed.

Lemma dn_nz_at : forall (l : list byte), (DgnSpec.nz_run l < length l)%nat ->
  DgnSpec.bz (nth (DgnSpec.nz_run l) l (Z_to_bv 8 0)) = 0.
Proof.
  induction l as [|x l IH]; cbn; [intros H; lia|].
  destruct (DgnSpec.bz x =? 0) eqn:E; intros H; cbn [nth].
  - apply Z.eqb_eq. exact E.
  - apply IH. lia.
Qed.

Lemma dn_nth_firstn : forall (l : list byte) k j d, (j < k)%nat -> nth j (firstn k l) d = nth j l d.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l j d H; [lia|].
  destruct l as [|x l]; [reflexivity|]. destruct j as [|j]; cbn; [reflexivity | apply IH; lia].
Qed.

Lemma dn_nth_skipn : forall (l : list byte) k j d, nth j (skipn k l) d = nth (k + j) l d.
Proof.
  intros l k. revert l. induction k as [|k IH]; intros l j d; [reflexivity|].
  destruct l as [|x l]; cbn; [destruct j; reflexivity | apply IH].
Qed.

(* A byte before the first NUL of the 9-byte window is not 0; the byte at the strz length, inside the window and the
   field, is 0. *)
Lemma dn_nth_nz : forall (body fld : list byte) (n j : nat), fld = skipn 24 body -> n = DgnSpec.strz_len fld ->
  (j < n)%nat -> bv_unsigned (nth (24 + j) body (Z_to_bv 8 0)) <> 0.
Proof.
  intros body fld n j -> -> H. unfold DgnSpec.strz_len in H.
  pose proof (dn_nz_lt _ _ H) as X.
  pose proof (dn_nz_le (firstn 9 (skipn 24 body))) as L. rewrite length_firstn in L.
  rewrite dn_nth_firstn in X by lia. rewrite dn_nth_skipn in X. exact X.
Qed.

Lemma dn_nth_nul : forall (body fld : list byte) (n : nat), fld = skipn 24 body -> n = DgnSpec.strz_len fld ->
  (n < 9)%nat -> (n < length fld)%nat -> bv_unsigned (nth (24 + n) body (Z_to_bv 8 0)) = 0.
Proof.
  intros body fld n -> -> H9 Hl. unfold DgnSpec.strz_len in *.
  assert (Lt : (DgnSpec.nz_run (firstn 9 (skipn 24 body)) < length (firstn 9 (skipn 24 body)))%nat)
    by (rewrite length_firstn; lia).
  pose proof (dn_nz_at _ Lt) as X.
  rewrite dn_nth_firstn in X by lia. rewrite dn_nth_skipn in X. exact X.
Qed.

(* ---- machine helpers ---- *)

Lemma dn_eqb : forall x y, 0 <= x < 2^64 -> 0 <= y < 2^64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof. intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma dn_eqb_w : forall v : word, bv_eqb v (Z_to_bv 64 0) = (bv_unsigned v =? 0).
Proof. intros v. unfold bv_eqb. rewrite (unsigned_lit 0) by lia. reflexivity. Qed.

Lemma dn_w0 : forall v : word, bv_unsigned v = 0 -> v = Z_to_bv 64 0.
Proof. intros v H. apply bv_eq. rewrite H. reflexivity. Qed.

Lemma dn_nw0 : forall v : word, bv_unsigned v <> 0 -> v <> Z_to_bv 64 0.
Proof. intros v H E. apply H. rewrite E. reflexivity. Qed.

(* the unsigned compares of the UBSan pointer checks (lib/U/Prog/T/desk_named.v dn_ltu) *)
Lemma dn_ltu : forall x y, 0 <= x < 2^64 -> bv_ltu (Z_to_bv 64 x) (Z_to_bv 64 y) = (x <? y mod 2^64).
Proof. intros x y Hx. unfold bv_ltu. rewrite !unsigned_lit_wrap. rewrite (Z.mod_small x) by lia. reflexivity. Qed.

Lemma dn_ltu_w : forall (v : word) x y, bv_unsigned v = x -> 0 <= y < 2^64 ->
  bv_ltu v (Z_to_bv 64 y) = (x <? y).
Proof. intros v x y Hv Hy. unfold bv_ltu. rewrite Hv, (unsigned_lit y) by lia. reflexivity. Qed.

(* a one-byte read of the body (check_refusal_submit_F.v rdc) *)
Lemma dn_rdc : forall m p (l : list byte) (n : nat) (a : Z),
  bytes_at rsegs m p l -> (n < length l)%nat -> a = p + Z.of_nat n ->
  ov_read_bytes rsegs m (wa a) 1 = Some [nth n l (Z_to_bv 8 0)].
Proof. intros m p l n a H Hn ->. apply rd1. apply (bytes_nth m p l n H Hn). Qed.

(* the shadow byte the check of a 1-byte load at p reads (check_refusal_submit_F.v shadow1) *)
Lemma dn_shadow1 : forall m p, addr_byte m p ->
  exists k : byte, mrd rsegs m (wa (p / 8 + 2147450880)) = Some k
                   /\ (bv_signed k = 0 \/ p mod 8 < bv_signed k).
Proof.
  intros m p (AP & k & MK & OK). unfold shadow_addr, ASAN_K in MK. exists k.
  split; [exact MK|]. unfold shadow_ok in OK. lia.
Qed.

(* the frame store keeps every shadow byte the checks read (check_refusal_submit_F.v addressable_tp) *)
Lemma dn_addr_byte_tp : forall (m m' : word -> option byte) lo hi a,
  munch [(lo, hi)] m m' -> app_mem lo -> app_mem (hi - 1) -> lo < hi -> hi <= lo + 16 ->
  addr_byte m a -> addr_byte m' a.
Proof.
  intros m m' lo hi a MU AL AH LH HL AB.
  pose proof AB as (AP & k & MK & OK). unfold shadow_addr, ASAN_K in MK.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in AL, AH, AP.
  split; [exact (proj1 AB)|]. exists k. split; [|exact OK].
  unfold shadow_addr, ASAN_K.
  apply (mrd_tp m m' lo hi (a / 8 + 2147450880) k MU); [Z.div_mod_to_equations; lia | | exact MK].
  Z.div_mod_to_equations; lia.
Qed.

Lemma dn_addressable_tp : forall (m m' : word -> option byte) lo hi p n,
  munch [(lo, hi)] m m' -> app_mem lo -> app_mem (hi - 1) -> lo < hi -> hi <= lo + 16 ->
  addressable m p n -> addressable m' p n.
Proof.
  intros m m' lo hi p n MU AL AH LH HL (P0 & N0 & PE & AB).
  split; [exact P0|]. split; [exact N0|]. split; [exact PE|].
  intros i Hi. exact (dn_addr_byte_tp m m' lo hi (p + i) MU AL AH LH HL (AB i Hi)).
Qed.

(* ---- the first run: the entry to the first call, or to the return with a0 = 0 ---- *)

Definition dn_post1 (ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (p : Z) (body : list byte)
    (ms' : machine_state) : Prop :=
  exists m1 : word -> option byte,
    munch [(bv_unsigned sp - 16, bv_unsigned sp)] m m1 /\ wmono rsegs m m1 /\
    ((DgnSpec.strz_len (skipn 24 body) <> 8%nat /\
      exists (r10 r11 r12 r13 r14 r15 r16 spx : word),
        ms' = MS (mkR ra spx gp tp t0 t1 t2 s0 s1 r10 r11 r12 r13 r14 r15 r16 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None m1 (seg_rom rsegs) /\
        bv_unsigned spx = bv_unsigned sp /\ bv_unsigned r10 = 0) \/
     (DgnSpec.strz_len (skipn 24 body) = 8%nat /\
      rw_cells rsegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] /\
      exists (r1 r2 r8 r10 r11 r12 r13 r14 r15 r16 : word),
        ms' = MS (mkR r1 r2 gp tp t0 t1 t2 r8 s1 r10 r11 r12 r13 r14 r15 r16 a7
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 DN_BCMP) fc None m1 (seg_rom rsegs) /\
        r1 = Z_to_bv 64 DN_RET1 /\ bv_unsigned r2 = bv_unsigned sp - 16 /\
        bv_unsigned r8 = p + 24 /\ bv_unsigned r10 = p + 24 /\
        bv_unsigned r11 = DgnTransportBCg.TRANS_STR_C24 /\ bv_unsigned r12 = 8)).

Lemma dn_run1_F :
  forall (RNG : ExecF.footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo p : Z) (body : list byte),
    0 < p -> p + Z.of_nat (length body) <= 2 ^ 63 ->
    bytes_at rsegs m p body ->
    (Nat.min 9 (S (DgnSpec.strz_len (skipn 24 body))) <= length (skipn 24 body))%nat ->
    stk rsegs m lo (bv_unsigned sp) -> lo + 16 <= bv_unsigned sp ->
    bytes_at rsegs m CELL_K (le8 (wa ASAN_K)) -> bytes_at rsegs m GOT_CELL_K (le8 (wa CELL_K)) ->
    app_mem (bv_unsigned sp - 16) -> app_mem (bv_unsigned sp - 1) ->
    off_stk sp 16 GOT_CELL_K 8 -> off_stk sp 16 CELL_K 8 -> off_stk sp 16 p (Z.of_nat (length body)) ->
    addressable m p (Z.of_nat (length body)) ->
    ExecF.rng RNG (bv_unsigned sp - 16) 16 -> ExecF.rng RNG GOT_CELL_K 8 -> ExecF.rng RNG CELL_K 8 ->
    (forall i, 0 <= i < Z.of_nat (length body) -> ExecF.rng RNG (shadow_addr (p + i)) 1) ->
    ExecF.rng RNG p (Z.of_nat (length body)) ->
    ExecF.evtF rsegs RNG
      (dn_post1 ra sp gp tp t0 t1 t2 s0 s1 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p body)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 DN_ENTRY) fc None m (seg_rom rsegs)).
Proof.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m lo p body Hp HPB HB HL ST HLO CK GCK APS1 APS2 DGC DCK DCP AW RFR RGC RCK RSW RCB.
  dn_pc.
  pose proof (u64_range sp) as Rsp.
  pose proof (stk_lo_nonneg _ _ _ _ ST) as L0.
  pose proof (bytes_at_bound rsegs m p body HB) as BB.
  set (fld := skipn 24 body) in *.
  set (n := DgnSpec.strz_len fld) in *.
  assert (Efld : fld = skipn 24 body) by reflexivity.
  assert (En : n = DgnSpec.strz_len fld) by reflexivity.
  assert (Lf : length fld = (length body - 24)%nat) by (unfold fld; apply length_skipn).
  assert (Hn9 : (n <= 9)%nat).
  { unfold n, DgnSpec.strz_len. pose proof (dn_nz_le (firstn 9 fld)) as X.
    rewrite length_firstn in X. lia. }
  unfold off_stk in DGC, DCK, DCP.
  unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in APS1, APS2.
  unfold CELL_K, ASAN_K in CK. unfold GOT_CELL_K, CELL_K in GCK.
  unfold GOT_CELL_K in DGC, RGC. unfold CELL_K in DCK, RCK.
  unfold shadow_addr, ASAN_K in RSW.
  (* keep the bytes_at facts off transport_chunks: they are carried past the two stores by hand *)
  pose proof (conj HB (conj CK GCK)) as HIDE. clear HB CK GCK.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  lazymatch goal with |- evtF _ _ ?Q _ => set (QQ := Q) end.
  carve_frame 16%nat ST.
  (* ---- 0x85100-0x85108: addi sp,sp,-16; sd ra,8(sp); sd s0,0(sp) ---- *)
  step. step. step.
  match goal with MU' : munch _ m ?m1 |- _ => rename MU' into MU1; rename m1 into m0 end.
  match goal with WM' : wmono rsegs m m0 |- _ => rename WM' into WM1 end.
  match goal with FR' : rw_cells rsegs m0 _ _ |- _ => rename FR' into FR0 end.
  destruct HIDE as (HB & CK & GCK).
  pose proof (bytes_tp m m0 _ _ p body MU1 ltac:(lia) HB) as HB0.
  pose proof (bytes_tp m m0 _ _ 706168 (le8 (wa 2147450880)) MU1 ltac:(rewrite length_le8; lia) CK) as CK0.
  pose proof (bytes_tp m m0 _ _ 670960 (le8 (wa 706168)) MU1 ltac:(rewrite length_le8; lia) GCK) as GCK0.
  clear HB CK GCK.
  pose proof (dn_addressable_tp m m0 _ _ p (Z.of_nat (length body)) MU1 APS1 APS2 ltac:(lia) ltac:(lia) AW)
    as AW0.
  clear AW.
  assert (RDG : ov_read_bytes rsegs m0 (wa 670960) 8 = Some (le8 (wa 706168))).
  { replace (wa 670960) with (wa (670960 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 670960 _ 0 8 GCK0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  assert (RDS : ov_read_bytes rsegs m0 (wa 706168) 8 = Some (le8 (wa 2147450880))).
  { replace (wa 706168) with (wa (706168 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m0 706168 _ 0 8 CK0 ltac:(lia)) by (rewrite length_le8; lia). reflexivity. }
  clear CK0 GCK0.
  pose proof AW0 as (AWp & AWn & AWe & AB).

  (* ---- 0x851a4 li a0,0, then the epilogue 0x851a8-0x851b4: the return with a0 = 0 ---- *)
  assert (RET0 : n <> 8%nat -> forall (x1 x8 x10 x11 x12 x13 x14 x15 x16 : word),
    evtF rsegs RNG QQ
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 x8 s1 x10 x11 x12 x13 x14 x15 x16 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x851a4) fc None m0 (seg_rom rsegs))).
  { intros N8 x1 x8 x10 x11 x12 x13 x14 x15 x16.
    step. step. step. step. step.
    apply evtF_done. unfold QQ, dn_post1. exists m0. split; [exact MU1|]. split; [exact WM1|].
    left. split; [exact N8|].
    do 8 eexists. split; [reflexivity|].
    split; [rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia|].
    reflexivity. }

  (* ---- 0x85134: the strz scan, i bytes read so far, all of them not NUL; a3 = ~s0 ---- *)
  assert (LOOP : forall (k : nat) (i : Z) (x10 x13 x15 x16 : word),
    bv_unsigned x13 = 18446744073709551615 - (p + 24) ->
    Z.of_nat k = 9 - i -> 0 <= i < 9 -> (Z.to_nat i <= n)%nat ->
    evtF rsegs RNG QQ
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 (p + 24)) s1
               x10 (Z_to_bv 64 i) (Z_to_bv 64 2147450880) x13 (Z_to_bv 64 9) x15 x16 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x85134) fc None m0 (seg_rom rsegs))).
  { induction k as [|k IH]; intros i x10 x13 x15 x16 H13 Hk Hi Hin; [lia|].
    assert (Li : (Z.to_nat i < length fld)%nat) by lia.
    (* 0x8514c: the byte load and the NUL test, once the check has passed *)
    assert (K2 : forall y15 y16 : word,
      evtF rsegs RNG QQ
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 (p + 24)) s1
                 (Z_to_bv 64 (p + 24 + i)) (Z_to_bv 64 i) (Z_to_bv 64 2147450880) x13 (Z_to_bv 64 9)
                 y15 y16 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x8514c) fc None m0 (seg_rom rsegs))).
    { intros y15 y16.
      pose proof (dn_rdc m0 p body (24 + Z.to_nat i) (p + 24 + i) HB0 ltac:(lia) ltac:(lia)) as RDi.
      set (b := nth (24 + Z.to_nat i) body (Z_to_bv 8 0)) in *.
      pose proof (byte_range b) as Rb.
      (* 0x8514c lbu a0,0(a0) *)
      step. clear RDi.
      (* 0x85150 beqz a0 *)
      step.
      unfold zxb. rewrite dn_eqb by lia.
      destruct (Nat.eq_dec (Z.to_nat i) n) as [Ein|Ein].
      - (* byte i is the NUL: n = i *)
        assert (Z0 : bv_unsigned b = 0).
        { unfold b. rewrite Ein. apply (dn_nth_nul body fld n Efld En); lia. }
        replace (bv_unsigned b =? 0) with true by (symmetry; apply Z.eqb_eq; exact Z0). cbn [negb].
        (* 0x8516c li a0,8 ; 0x85170 bne a1,a0 *)
        step. step.
        rewrite dn_eqb by lia.
        destruct (Z.eqb_spec i 8) as [E8|E8]; cbn [negb].
        + (* the name is 8 bytes long: 0x85174-0x85184, the first call of bcmp *)
          assert (N8 : n = 8%nat) by lia.
          step. step. step. step. step.
          apply evtF_done. unfold QQ, dn_post1. exists m0. split; [exact MU1|]. split; [exact WM1|].
          right. split; [exact N8|]. split; [exact FR0|].
          do 10 eexists. split; [reflexivity|].
          split; [reflexivity|].
          split; [rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia|].
          split; [rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia|].
          split; [rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia|].
          split; reflexivity.
        + apply RET0. lia.
      - (* byte i is not NUL: i < n *)
        assert (Lt : (Z.to_nat i < n)%nat) by lia.
        assert (NZ : bv_unsigned b <> 0) by (unfold b; exact (dn_nth_nz body fld n (Z.to_nat i) Efld En Lt)).
        replace (bv_unsigned b =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ). cbn [negb].
        (* 0x85154 addi a1,a1,1 ; 0x85158 bne a1,a4 *)
        step. step.
        rewrite dn_eqb by lia.
        destruct (Z.eqb_spec (i + 1) 9) as [E9|E9]; cbn [negb].
        + (* no NUL in the 9 bytes: 0x8515c j 0x851a4 *)
          step. apply RET0. lia.
        + apply (IH (i + 1)); [exact H13 | lia | lia | lia]. }
    (* 0x85134 bltu a3,a1: ~s0 < i would be s0 + i >= 2^64, and s0 + i < p + length body <= 2^63 *)
    step.
    rewrite (dn_ltu_w x13 _ i H13 ltac:(lia)).
    replace (18446744073709551615 - (p + 24) <? i) with false by (symmetry; apply Z.ltb_ge; lia).
    cbv iota.
    (* 0x85138 add a0,s0,a1 *)
    step.
    (* 0x8513c-0x85144: the shadow byte of p + 24 + i *)
    pose proof (AB (24 + i) ltac:(lia)) as ABi.
    pose proof (RSW (24 + i) ltac:(lia)) as RSi.
    replace (p + (24 + i)) with (p + 24 + i) in ABi, RSi by lia.
    destruct (dn_shadow1 m0 (p + 24 + i) ABi) as (ki & MKi & SKi).
    pose proof (Z.mod_pos_bound (p + 24 + i) 8 ltac:(lia)) as MBi.
    step. gen_shr (Z_to_bv 64 (p + 24 + i)) gi Gi.
    rewrite (unsigned_lit (p + 24 + i) ltac:(lia)) in Gi.
    step. gen_addi gi hi Hi'.
    pose proof (rng_sub' RNG _ _ (bv_unsigned hi) 1 RSi ltac:(lia)) as RHi.
    pose proof (rdw0 m0 hi _ _ MKi ltac:(lia)) as Ri'.
    step. clear Ri'.
    (* 0x85148 bnez a5 *)
    step. rewrite sxb_eq0.
    destruct SKi as [Ci|Ci].
    + rewrite (proj2 (Z.eqb_eq _ _) Ci). cbn [negb]. apply K2.
    + rewrite (proj2 (Z.eqb_neq (bv_signed ki) 0) ltac:(lia)). cbn [negb].
      (* 0x85160 andi a6,a0,7 ; 0x85164 blt a6,a5 *)
      step. rewrite land7, (unsigned_lit (p + 24 + i) ltac:(lia)).
      step. rewrite (lts_low ((p + 24 + i) mod 8) ki ltac:(lia)), (proj2 (Z.ltb_lt _ _) Ci). cbv iota.
      apply K2. }

  (* ---- 0x8510c beqz a0: p <> 0 ---- *)
  step. rewrite dn_eqb by lia.
  replace (p =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbv iota.
  (* ---- 0x85110 li a1,-24 ; 0x85114 bgeu a0,a1: p < 2^64 - 24 ---- *)
  step. step.
  rewrite dn_ltu by lia.
  match goal with |- context [p <? ?y] =>
    replace (p <? y) with true
      by (symmetry; apply Z.ltb_lt; replace y with 18446744073709551592 by reflexivity; lia)
  end.
  cbn [negb].
  (* ---- 0x85118 li a1,0 ; 0x8511c-0x85124 a2 = the shadow base ; 0x85128 addi s0,a0,24 ;
     0x8512c not a3,s0 ; 0x85130 li a4,9 ---- *)
  step. step. step. step. step. step. step.
  eapply (LOOP 9%nat 0); [| lia | lia | lia].
  rewrite ?unsigned_lit_wrap.
  rewrite ?(Z.mod_small (p + 24)) by lia.
  rewrite zb_lxor_ones by lia.
  apply Z.mod_small. lia.
Qed.

(* ---- the second run: the first call's return ---- *)

Lemma dn_run2_F :
  forall (RNG : ExecF.footprint)
         (x1 sp2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 cs0 cra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    16 <= bv_unsigned sp2 -> bv_unsigned sp2 + 16 <= 2 ^ 63 ->
    rw_cells rsegs m (bv_unsigned sp2) [C8 cs0; C8 cra] ->
    ExecF.rng RNG (bv_unsigned sp2) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' =>
         (v = Z_to_bv 64 0 /\
          exists (r10 spx : word),
            ms' = MS (mkR cra spx x3 x4 x5 x6 x7 cs0 x9 r10 x11 x12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (ret_pc cra) fc None m (seg_rom rsegs) /\
            bv_unsigned spx = bv_unsigned sp2 + 16 /\ bv_unsigned r10 = DgnTransportBCg.TRANS_SPEC_C24) \/
         (v <> Z_to_bv 64 0 /\
          exists (r1 r10 r11 r12 : word),
            ms' = MS (mkR r1 sp2 x3 x4 x5 x6 x7 x8 x9 r10 r11 r12 x13 x14 x15 x16 x17
                          x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                     F (Z_to_bv 64 DN_BCMP) fc None m (seg_rom rsegs) /\
            r1 = Z_to_bv 64 DN_RET2 /\ bv_unsigned r10 = bv_unsigned x8 /\
            bv_unsigned r11 = DgnTransportBCg.TRANS_STR_PC /\ bv_unsigned r12 = 8))
      (MS (mkR x1 sp2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 DN_RET1) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 sp2 x3 x4 x5 x6 x7 x8 x9 v x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 cs0 cra F fc m H16 Hhi FR RFR.
  dn_pc.
  pose proof (u64_range sp2) as Rsp. pose proof (u64_range x8) as R8.
  (* 0x85188 beqz a0 *)
  step. rewrite dn_eqb_w.
  destruct (Z.eqb_spec (bv_unsigned v) 0) as [V0|V0]; cbv iota.
  - (* 0x851b8-0x851c0: a0 = SPEC_C24, j 0x851a8; the epilogue *)
    step. step. step. step. step. step. step.
    apply evtF_done. left. split; [exact (dn_w0 v V0)|].
    do 2 eexists. split; [reflexivity|].
    split; [rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia | reflexivity].
  - (* 0x8518c-0x8519c: the second call of bcmp *)
    step. step. step. step. step.
    apply evtF_done. right. split; [exact (dn_nw0 v V0)|].
    do 4 eexists. split; [reflexivity|].
    split; [reflexivity|].
    split; [rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia|].
    split; reflexivity.
Qed.

(* ---- the third run: the second call's return ---- *)

Lemma dn_run3_F :
  forall (RNG : ExecF.footprint)
         (x1 sp2 x3 x4 x5 x6 x7 x8 x9 w x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
          x28 x29 x30 x31 cs0 cra : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    16 <= bv_unsigned sp2 -> bv_unsigned sp2 + 16 <= 2 ^ 63 ->
    rw_cells rsegs m (bv_unsigned sp2) [C8 cs0; C8 cra] ->
    ExecF.rng RNG (bv_unsigned sp2) 16 ->
    ExecF.evtF rsegs RNG
      (fun ms' => exists (r10 spx : word),
         ms' = MS (mkR cra spx x3 x4 x5 x6 x7 cs0 x9 r10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                  F (ret_pc cra) fc None m (seg_rom rsegs) /\
         bv_unsigned spx = bv_unsigned sp2 + 16 /\
         ((w = Z_to_bv 64 0 /\ bv_unsigned r10 = DgnTransportBCg.TRANS_SPEC_PC) \/
          (w <> Z_to_bv 64 0 /\ bv_unsigned r10 = 0)))
      (MS (mkR x1 sp2 x3 x4 x5 x6 x7 x8 x9 w x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 DN_RET2) fc None m (seg_rom rsegs)).
Proof.
  intros RNG x1 sp2 x3 x4 x5 x6 x7 x8 x9 w x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
    x28 x29 x30 x31 cs0 cra F fc m H16 Hhi FR RFR.
  dn_pc.
  pose proof (u64_range sp2) as Rsp.
  (* 0x851a0 beqz a0 *)
  step. rewrite dn_eqb_w.
  destruct (Z.eqb_spec (bv_unsigned w) 0) as [W0|W0]; cbv iota.
  - (* 0x851c4-0x851cc: a0 = SPEC_PC, j 0x851a8; the epilogue *)
    step. step. step. step. step. step. step.
    apply evtF_done. do 2 eexists. split; [reflexivity|].
    split; [rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia|].
    left. split; [exact (dn_w0 w W0) | reflexivity].
  - (* 0x851a4 li a0,0; the epilogue *)
    step. step. step. step. step.
    apply evtF_done. do 2 eexists. split; [reflexivity|].
    split; [rewrite ?unsigned_lit_wrap; Z.div_mod_to_equations; lia|].
    right. split; [exact (dn_nw0 w W0) | reflexivity].
Qed.

End DNRun.

(* ======== the walk ======== *)

From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
  YG00 YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YI16 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI5b YI5c.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import PropExec MState Mem Cells Step Regs6ss.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Lib Require Import Frame ExecF.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require LeafCgKit LeafCgFacts CgBNoTwin.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportFevt YC85.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TImgB desk_named_cg.
Open Scope Z_scope.

Ltac dn_lia := unfold DNAMED_STK, DNAMED_FRAME, ESTACK in *; lia.

(* ---- the model (lib/TModel/TCb.v desk_named_m), no machine (lib/Prog/T/desk_named.v:15-37, 79-86) ---- *)

(* what desk_named_m returns for the strz length n of the name field fld *)
Definition dn_r (I : TI.timg) (n : nat) (fld : list byte) : Z :=
  if (n =? 8)%nat && TC.beq_bytes (firstn n fld) TC.C24_NAME then TI.ti_spec_c24 I
  else if (n =? 8)%nat && TC.beq_bytes (firstn n fld) TC.PC_NAME then TI.ti_spec_pc I
  else 0.

Lemma dn_model : forall I Bw body Bw' r, TC.desk_named_m I Bw body = Some (Bw', r) ->
  Bw' = Bw /\ (Nat.min 9 (S (DSpec.strz_len (skipn 24 body))) <= length (skipn 24 body))%nat /\
  r = dn_r I (DSpec.strz_len (skipn 24 body)) (skipn 24 body).
Proof.
  intros I Bw body Bw' r H. unfold TC.desk_named_m, TC.list_strz_len, TC.SPEC_ANN_NAME in H. cbv zeta in H.
  change (Z.to_nat 24) with 24%nat in H. unfold dn_r. revert H.
  destruct (length (skipn 24 body) <? Nat.min 9 (S (DSpec.strz_len (skipn 24 body))))%nat eqn:E; [discriminate|].
  apply Nat.ltb_ge in E. intros H. cbv beta iota in H. revert H.
  destruct ((DSpec.strz_len (skipn 24 body) =? 8)%nat
              && TC.beq_bytes (firstn (DSpec.strz_len (skipn 24 body)) (skipn 24 body)) TC.C24_NAME);
    [|destruct ((DSpec.strz_len (skipn 24 body) =? 8)%nat
                  && TC.beq_bytes (firstn (DSpec.strz_len (skipn 24 body)) (skipn 24 body)) TC.PC_NAME)];
    intros H;
    pose proof (f_equal (fun o : option (list byte * Z) => match o with Some (b, _) => b | None => Bw end) H) as HB;
    pose proof (f_equal (fun o : option (list byte * Z) => match o with Some (_, z) => z | None => 0 end) H) as HR;
    cbv beta iota in HB, HR;
    (split; [symmetry; exact HB | split; [exact E | symmetry; exact HR]]).
Qed.

Lemma dn_beq_true : forall a b, TWorld.zs a = TWorld.zs b -> TC.beq_bytes a b = true.
Proof.
  intros a b E. unfold TC.beq_bytes.
  destruct (list_eq_dec Z.eq_dec (TWorld.zs a) (TWorld.zs b)); [reflexivity | contradiction].
Qed.

Lemma dn_beq_false : forall a b, TWorld.zs a <> TWorld.zs b -> TC.beq_bytes a b = false.
Proof.
  intros a b E. unfold TC.beq_bytes.
  destruct (list_eq_dec Z.eq_dec (TWorld.zs a) (TWorld.zs b)); [contradiction | reflexivity].
Qed.

(* desk_named_m's four answers *)
Lemma dn_r_ne8 : forall I n fld, n <> 8%nat -> dn_r I n fld = 0.
Proof. intros I n fld H. unfold dn_r. destruct (Nat.eqb_spec n 8); [contradiction | reflexivity]. Qed.

Lemma dn_r_c24 : forall fld, TWorld.zs (firstn 8 fld) = TWorld.zs TC.C24_NAME ->
  dn_r timg_B 8 fld = TRANS_SPEC_C24.
Proof. intros fld H. unfold dn_r. rewrite (dn_beq_true _ _ H). reflexivity. Qed.

Lemma dn_r_pc : forall fld, TWorld.zs (firstn 8 fld) <> TWorld.zs TC.C24_NAME ->
  TWorld.zs (firstn 8 fld) = TWorld.zs TC.PC_NAME -> dn_r timg_B 8 fld = TRANS_SPEC_PC.
Proof. intros fld H1 H2. unfold dn_r. rewrite (dn_beq_false _ _ H1), (dn_beq_true _ _ H2). reflexivity. Qed.

Lemma dn_r_none : forall fld, TWorld.zs (firstn 8 fld) <> TWorld.zs TC.C24_NAME ->
  TWorld.zs (firstn 8 fld) <> TWorld.zs TC.PC_NAME -> dn_r timg_B 8 fld = 0.
Proof. intros fld H1 H2. unfold dn_r. rewrite (dn_beq_false _ _ H1), (dn_beq_false _ _ H2). reflexivity. Qed.

(* bcmp's equality test over 8 bytes, against two byte lists *)
Lemma dn_cmp_iff : forall (l1 l2 : list byte) (f g : Z -> option Z),
  length l1 = 8%nat -> length l2 = 8%nat ->
  (forall i, 0 <= i < 8 -> f i = Some (bv_unsigned (nth (Z.to_nat i) l1 (Z_to_bv 8 0)))) ->
  (forall i, 0 <= i < 8 -> g i = Some (bv_unsigned (nth (Z.to_nat i) l2 (Z_to_bv 8 0)))) ->
  ((forall i, 0 <= i < 8 -> f i = g i) <-> TWorld.zs l1 = TWorld.zs l2).
Proof.
  intros l1 l2 f g L1 L2 HF HG. unfold TWorld.zs. split.
  - intros E. apply nth_ext with (d := bv_unsigned (Z_to_bv 8 0)) (d' := bv_unsigned (Z_to_bv 8 0));
      [rewrite !length_map; lia|].
    intros j Hj. rewrite length_map in Hj. rewrite !map_nth.
    pose proof (E (Z.of_nat j) ltac:(lia)) as Ej.
    rewrite (HF (Z.of_nat j) ltac:(lia)), (HG (Z.of_nat j) ltac:(lia)) in Ej.
    rewrite Nat2Z.id in Ej. injection Ej as Ej. exact Ej.
  - intros E i Hi. rewrite (HF i Hi), (HG i Hi). f_equal.
    pose proof (f_equal (fun l => nth (Z.to_nat i) l (bv_unsigned (Z_to_bv 8 0))) E) as Ei.
    cbv beta in Ei. rewrite !map_nth in Ei. exact Ei.
Qed.

Lemma dn_nth_fs : forall (body : list byte) j d, (j < 8)%nat ->
  nth j (firstn 8 (skipn 24 body)) d = nth (24 + j) body d.
Proof. intros body j d H. rewrite DNRun.dn_nth_firstn by exact H. apply DNRun.dn_nth_skipn. Qed.

(* garr8's bytes, as byte values (fuzz_decode's lib/A/Prog/check_events_fields_cg_bridge.v cw_nth_map_bz,
   cw_b8_bz) *)
Lemma dn_nth_map_bz : forall (l : list byte) i, (i < length l)%nat ->
  nth i (map DSpec.bz l) 0 = DSpec.bz (nth i l (Z_to_bv 8 0)).
Proof.
  induction l as [|b l IH]; intros i Hi; [cbn in Hi; lia|].
  destruct i as [|i]; [reflexivity|]. cbn [map nth length] in *. apply IH. lia.
Qed.

Lemma dn_b8_bz : forall b : byte, Z_to_bv 8 (le_byte (DSpec.bz b) 1 0) = b.
Proof.
  intros b. pose proof (bv_unsigned_in_range 8 b) as Hbr. unfold bv_modulus in Hbr.
  change (2 ^ Z.of_N 8) with 256 in Hbr. unfold le_byte, DSpec.bz.
  change (8 * Z.of_nat 1) with 8. change (8 * Z.of_nat 0) with 0. rewrite Z.shiftr_0_r.
  change (2 ^ 8) with 256. rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  rewrite (Z.mod_small (bv_unsigned b) 256) by lia.
  apply bv_eq. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus.
  change (2 ^ Z.of_N 8) with 256. rewrite Z.mod_small by lia. reflexivity.
Qed.

(* ---- the image's two strings (decided over the image) ---- *)

Lemma dn_in_ro_c24 : forall i, 0 <= i < 8 -> trans_in_ro_rd (TRANS_STR_C24 + i).
Proof.
  intros i Hi. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_STR_C24, 9). split.
  - unfold TRANS_RO_RD. apply in_or_app. right. unfold TRANS_RO_GLOBALS. do 5 right. left. reflexivity.
  - unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma dn_in_ro_pc : forall i, 0 <= i < 8 -> trans_in_ro_rd (TRANS_STR_PC + i).
Proof.
  intros i Hi. unfold trans_in_ro_rd. apply Exists_exists. exists (TRANS_STR_PC, 9). split.
  - unfold TRANS_RO_RD. apply in_or_app. right. unfold TRANS_RO_GLOBALS. do 6 right. left. reflexivity.
  - unfold in_zr. cbn [fst snd]. lia.
Qed.

Lemma dn_rom_c24 : forall i, 0 <= i < 8 ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (TRANS_STR_C24 + i)))
  = Some (bv_unsigned (nth (Z.to_nat i) TC.C24_NAME (Z_to_bv 8 0))).
Proof.
  intros i Hi.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst i; vm_compute; reflexivity.
Qed.

Lemma dn_rom_pc : forall i, 0 <= i < 8 ->
  option_map (fun b : byte => bv_unsigned b) (YK11.seg_rom tfibsegs (Z_to_bv 64 (TRANS_STR_PC + i)))
  = Some (bv_unsigned (nth (Z.to_nat i) TC.PC_NAME (Z_to_bv 8 0))).
Proof.
  intros i Hi.
  assert (Hc : i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst i; vm_compute; reflexivity.
Qed.

Section Walk.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation ajournalB := (@ajournal rc YE2k.tfib_sink_head segs B).

Hypothesis HCELLS : transport_cells B.
Hypothesis HDNC : trans_dnamed_cells B.
Hypothesis LAWS : AR_laws segs B.
Hypothesis MTL : ameter_laws MT.
Hypothesis ABCMPH : forall fx' : YK11.FPState,
  @abcmp_realizes fx' rc segs B (transportb_sigma TB___interceptor_trampoline_bcmp).

(* ---- the run's final state (lib/A/Prog/DgnTransportCgRun.v decode_ms_shape / decode_ms_reg; image B's kit states
   them as TransportFevt.v decode_eqv_mkst / decode_getr_xeqv) ---- *)

(* A state ms_eqv to decode's MS form with cgif's float state is cgif's mkst state of its own register map. *)
Lemma dn_ms_shape : forall (R : bvmap 5 word) (pc : word) (m : word -> option byte) (ms' : machine_state),
  ms_eqv (MS R (@YK11.fp_regs fx) pc (@YK11.fp_csr fx) None m (YK11.seg_rom segs)) ms' ->
  ms' = @YK11.mkst fx (ms_regs ms') pc m (YK11.seg_rom segs).
Proof.
  intros R pc m [r f p sv rv fc mm ro] (_ & Hf & Hp & Hs & Hr & Hc & Hm & Hro).
  cbn [MS ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_mem ms_rom] in *.
  subst. reflexivity.
Qed.

(* ... and its registers are R's. *)
Lemma dn_ms_reg : forall (R : bvmap 5 word) F pc fc rv m ro (ms' : machine_state) (r : bv 5),
  ms_eqv (MS R F pc fc rv m ro) ms' -> YK11.getr (ms_regs ms') r = YK11.getr R r.
Proof. intros R F pc fc rv m ro ms' r EQV. exact (decode_getr_xeqv R (ms_regs ms') (proj1 EQV) r). Qed.

(* ---- reading a range: the record's constant cells, the runtime's view, a kept view ---- *)

(* A byte the view reads is not hidden (lib/A/Prog/DgnTransportCgRun.v decode_aview_vis). *)
Lemma dn_aview_vis : forall (W : world segs) mem a v,
  aview segs (w_H W) mem a = Some v -> w_H W (Z_to_bv 64 a) = false.
Proof.
  intros W mem a v H. destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (@w_Hoff segs W _ E) as F.
  unfold aview, YP09.mbyte, mrestrict in H. rewrite E in H.
  unfold YK11.seg_rom, memory_read in H. cbn [Z.of_N] in H. rewrite F in H. discriminate H.
Qed.

(* A one-byte constant cell of the record is visible at every AR state (YG0n.v ARm am_const). *)
Lemma dn_const_vis : forall ly S (W : world segs) mem md a v,
  AR segs B ly S W mem md -> In (z1 (ANum a) v) (as_const B ly) -> aview segs (w_H W) mem a <> None.
Proof.
  intros ly S W mem md a v [HM _] Hin.
  assert (HK : Forall (cell_holds B ly (aview segs (w_H W) mem)) (as_const B ly)) by (eapply am_const; exact HM).
  pose proof (proj1 (Forall_forall _ _) HK _ Hin) as Hc.
  unfold z1, c1, cell_holds in Hc. cbn [aeval c_at c_w c_val] in Hc.
  specialize (Hc 0%nat ltac:(lia)). cbn [Z.of_nat] in Hc. rewrite Z.add_0_r in Hc. rewrite Hc. discriminate.
Qed.

(* A read range keeps its facts at a memory whose view agrees outside a window [lo, hi) above the shadow map that
   the range avoids: its bytes and the shadow bytes of its hull all lie outside the window. *)
Lemma dn_rd_keep : forall (W : world segs) m m' q n lo hi,
  decode_rd_ok W m q n -> 0 < n -> kHighShadowEnd <= lo -> (q + n <= lo \/ hi <= q) ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lo <= a < hi) -> aview segs (w_H W) m' a = aview segs (w_H W) m a) ->
  decode_rd_ok W m' q n.
Proof.
  intros W m m' q n lo hi (Hv & Hra & Hh & Hm & H0 & H63) Hn Hlo Hd K.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HQ : q + n <= kHighMemEnd) by (unfold amem_range in Hm; lia).
  split.
  { intros a Ha. rewrite (K a ltac:(lia) ltac:(lia)). exact (Hv a Ha). }
  split.
  { intros x Hx. destruct (Hra x Hx) as (s & Hs & Hok). exists s. split; [|exact Hok].
    assert (Hb : kLowMemEnd <= shadow_of_addr SHADOW_OFF x < kHighShadowEnd)
      by (exact (shadow_addr_bounds x ltac:(lia))).
    rewrite (K (shadow_of_addr SHADOW_OFF x) ltac:(lia) ltac:(lia)). exact Hs. }
  split.
  { intros s Hs.
    pose proof (shadow_addr_bounds q ltac:(lia)) as [SBq1 SBq2].
    pose proof (shadow_addr_bounds (q + n - 1) ltac:(lia)) as [SBn1 SBn2].
    pose proof (Z.div_mod (shadow_addr q) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_addr q) 8 ltac:(lia)).
    pose proof (Z.div_mod (shadow_addr (q + n - 1)) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (shadow_addr (q + n - 1)) 8 ltac:(lia)).
    assert (Hs1 : 0 <= s < kHighShadowEnd) by (unfold kHighShadowEnd in *; lia).
    rewrite (K s ltac:(lia) ltac:(lia)). exact (Hh s Hs). }
  split; [exact Hm|]. split; [exact H0 | exact H63].
Qed.

(* ---- one call: the caller's journal, its state and its premises ---- *)

Section Call.
Variables (STK sp0 : Z) (FP : list (Z * Z)) (ly : alayout) (S : astate) (W0 : world segs)
  (mem0 : word -> option byte) (md0 : Model) (own : list (Z * Z)) (lyc : alayout) (Sc : astate)
  (W : world segs) (memc : word -> option byte) (mdc : Model) (k : Z) (regs : bvmap 5 word)
  (p r : Z) (body : list byte) (Bw Bw' : list byte).

Hypothesis HJ : ajournalB STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k.
Hypothesis HRET : YK0s.ret_ok (YK11.getr regs 1).
Hypothesis HRA4 : 4096 <= raZ regs.
Hypothesis HGP : YK11.getr regs 3 = w64 (as_gp B).
Hypothesis HTP : YK11.getr regs 4 = w64 (as_tp B).
Hypothesis H10 : YK11.getr regs 10 = w64 p.
Hypothesis HAL : spZ regs mod 16 = 0.
Hypothesis HWLO : sp0 - STK <= spZ regs - DNAMED_STK.
Hypothesis HWHI : spZ regs <= sp0.
Hypothesis HP0 : 0 < p.
Hypothesis GBB : garr8 segs (mrestrict (w_H W) memc) p (map DSpec.bz body).
Hypothesis HSRC : trans_src_ok B lyc Sc W memc p (Z.of_nat (length body)).
Hypothesis OWB : decode_off_win regs DNAMED_STK p (Z.of_nat (length body)).
Hypothesis HROM : trans_rom_view_rd W memc.
Hypothesis HM : TC.desk_named_m timg_B Bw body = Some (Bw', r).
Hypothesis HNEV : st_nev S + k + DNAMED_EV <= EV_MAX.

Lemma dn_AR : AR segs B lyc Sc W memc mdc.
Proof. destruct HJ as (HAR & _). exact HAR. Qed.

Lemma dn_stk_ok : astk_ok STK ly sp0.
Proof.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & _). exact HS.
Qed.

Lemma dn_pres : forall a, sp0 - STK <= a < sp0 -> apresent (w_H W) memc a.
Proof.
  destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _). exact HP.
Qed.

Lemma dn_sp_rng : YM05.alloc_ceiling + DNAMED_STK <= spZ regs /\ spZ regs <= 2 ^ 47.
Proof. pose proof dn_stk_ok as (H16 & Hstk0 & Hceil & Hlo & Hhi & H47 & _). lia. Qed.

Lemma dn_mod : Bw' = Bw /\
  (Nat.min 9 (Datatypes.S (DSpec.strz_len (skipn 24 body))) <= length (skipn 24 body))%nat /\
  r = dn_r timg_B (DSpec.strz_len (skipn 24 body)) (skipn 24 body).
Proof. exact (dn_model _ _ _ _ _ HM). Qed.

Lemma dn_len : 25 <= Z.of_nat (length body).
Proof. pose proof dn_mod as (_ & HL & _). rewrite length_skipn in HL. lia. Qed.

(* the body's facts, through the kit's trans_src_ok_rd *)
Lemma dn_rdb : decode_rd_ok W memc p (Z.of_nat (length body)).
Proof. exact (trans_src_ok_rd B LAWS lyc Sc W memc mdc p _ dn_AR HSRC ltac:(pose proof dn_len; lia)). Qed.

(* the body's bytes, as the view reads them (garr8) *)
Lemma dn_view_body : forall i, 0 <= i < Z.of_nat (length body) ->
  aview segs (w_H W) memc (p + i) = Some (bv_unsigned (nth (Z.to_nat i) body (Z_to_bv 8 0))).
Proof.
  intros i Hi. destruct (GBB (Z.to_nat i) ltac:(rewrite length_map; lia)) as [HV1 _].
  specialize (HV1 0%nat ltac:(lia)). cbn [Z.of_nat] in HV1. rewrite Z.add_0_r, Z2Nat.id in HV1 by lia.
  unfold aview. cbv beta. rewrite HV1. cbn [option_map]. f_equal. f_equal.
  rewrite (dn_nth_map_bz body (Z.to_nat i) ltac:(lia)). apply dn_b8_bz.
Qed.

(* the body's bytes as the footprint run reads them (TransportFevt.v decode_garr8_bytes) *)
Lemma dn_bytes : bytes_at rsegs memc p body.
Proof.
  pose proof dn_rdb as (Hv & _ & _ & _ & H0 & H63).
  apply (decode_garr8_bytes (w_H W) memc p body); [lia | lia | | exact GBB].
  intros j Hj.
  destruct (aview segs (w_H W) memc (p + Z.of_nat j)) as [v|] eqn:Ev; [exact (dn_aview_vis W memc _ v Ev)|].
  exfalso. exact (Hv (p + Z.of_nat j) ltac:(lia) Ev).
Qed.

(* the two strings, as the view reads them at the entry state (trans_rom_view_rd) *)
Lemma dn_view_c24 : forall i, 0 <= i < 8 ->
  aview segs (w_H W) memc (TRANS_STR_C24 + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.C24_NAME (Z_to_bv 8 0))).
Proof. intros i Hi. rewrite (HROM _ (dn_in_ro_c24 i Hi)). exact (dn_rom_c24 i Hi). Qed.

Lemma dn_view_pc : forall i, 0 <= i < 8 ->
  aview segs (w_H W) memc (TRANS_STR_PC + i) = Some (bv_unsigned (nth (Z.to_nat i) TC.PC_NAME (Z_to_bv 8 0))).
Proof. intros i Hi. rewrite (HROM _ (dn_in_ro_pc i Hi)). exact (dn_rom_pc i Hi). Qed.

(* A string's read facts at the entry state: its bytes visible; its shadow byte 0 (the record's zero-shadow row,
   transport_cells); the 8 shadow bytes of its hull visible. On image B the two strings lie in two aligned groups:
   TRANS_STR_C24's hull [0x7fffc208, 0x7fffc210) holds the shadow of SPEC_OUI (its partial-granule cell, transport_cells),
   three guard cells, the string's zero-shadow byte and partial-granule cell (transport_cells) and two guard cells;
   TRANS_STR_PC's hull [0x7fffc210, 0x7fffc218) the string's zero-shadow byte and partial-granule cell, two guard cells,
   op_frame.CMD's partial-granule cell (transport_cells) and three guard cells. The ten guard cells are
   trans_dnamed_cells. *)
Lemma dn_str_rd : forall q, (q = TRANS_STR_C24 \/ q = TRANS_STR_PC) ->
  (forall i, 0 <= i < 8 -> aview segs (w_H W) memc (q + i) <> None) ->
  decode_rd_ok W memc q 8.
Proof.
  intros q Hq Hv.
  pose proof dn_AR as HAR.
  destruct (HCELLS lyc) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                             _ & _ & _ & _ & OUI & Z24 & C24c & ZPC & PCc & CMD & _).
  destruct (HDNC lyc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
  assert (Z0 : forall T, T = TRANS_STR_C24 \/ T = TRANS_STR_PC ->
            aview segs (w_H W) memc (BCells.shadow_addr T) = Some 0).
  { intros T [-> | ->].
    - exact (decode_zshadow_rd B lyc Sc W memc mdc TRANS_STR_C24 (TRANS_STR_C24 + 8) TRANS_STR_C24 HAR
               eq_refl ltac:(lia) ltac:(lia) Z24).
    - exact (decode_zshadow_rd B lyc Sc W memc mdc TRANS_STR_PC (TRANS_STR_PC + 8) TRANS_STR_PC HAR
               eq_refl ltac:(lia) ltac:(lia) ZPC). }
  split.
  { intros a Ha. replace a with (q + (a - q)) by lia. apply Hv. lia. }
  split.
  { intros x Hx. exists 0. split; [|left; reflexivity].
    replace (shadow_of_addr SHADOW_OFF x) with (BCells.shadow_addr q).
    - exact (Z0 q Hq).
    - destruct Hq as [-> | ->]; unfold shadow_of_addr, BCells.shadow_addr, SHADOW_OFF, BCells.ASAN_K,
        TRANS_STR_C24, TRANS_STR_PC in *; Z.div_mod_to_equations; lia. }
  split.
  { intros s Hs. destruct Hq as [-> | ->].
    - assert (Hs' : 2147467784 <= s < 2147467792).
      { unfold shadow_addr, SHADOW_OFF, TRANS_STR_C24 in Hs. Z.div_mod_to_equations; lia. }
      assert (Hc : s = 2147467784 \/ s = 2147467785 \/ s = 2147467786 \/ s = 2147467787 \/
                   s = 2147467788 \/ s = 2147467789 \/ s = 2147467790 \/ s = 2147467791) by lia.
      destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
      + change 2147467784 with (BCells.shadow_addr TRANS_SPEC_OUI). exact (dn_const_vis _ _ _ _ _ _ _ HAR OUI).
      + change 2147467785 with (BCells.shadow_addr (TRANS_SPEC_OUI + 8)). exact (dn_const_vis _ _ _ _ _ _ _ HAR D1).
      + change 2147467786 with (BCells.shadow_addr (TRANS_SPEC_OUI + 16)). exact (dn_const_vis _ _ _ _ _ _ _ HAR D2).
      + change 2147467787 with (BCells.shadow_addr (TRANS_SPEC_OUI + 24)). exact (dn_const_vis _ _ _ _ _ _ _ HAR D3).
      + change 2147467788 with (BCells.shadow_addr TRANS_STR_C24).
        rewrite (Z0 _ (or_introl eq_refl)). discriminate.
      + change 2147467789 with (BCells.shadow_addr (TRANS_STR_C24 + 8)). exact (dn_const_vis _ _ _ _ _ _ _ HAR C24c).
      + change 2147467790 with (BCells.shadow_addr (TRANS_STR_C24 + 16)). exact (dn_const_vis _ _ _ _ _ _ _ HAR D4).
      + change 2147467791 with (BCells.shadow_addr (TRANS_STR_C24 + 24)). exact (dn_const_vis _ _ _ _ _ _ _ HAR D5).
    - assert (Hs' : 2147467792 <= s < 2147467800).
      { unfold shadow_addr, SHADOW_OFF, TRANS_STR_PC in Hs. Z.div_mod_to_equations; lia. }
      assert (Hc : s = 2147467792 \/ s = 2147467793 \/ s = 2147467794 \/ s = 2147467795 \/
                   s = 2147467796 \/ s = 2147467797 \/ s = 2147467798 \/ s = 2147467799) by lia.
      destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]].
      + change 2147467792 with (BCells.shadow_addr TRANS_STR_PC).
        rewrite (Z0 _ (or_intror eq_refl)). discriminate.
      + change 2147467793 with (BCells.shadow_addr (TRANS_STR_PC + 8)). exact (dn_const_vis _ _ _ _ _ _ _ HAR PCc).
      + change 2147467794 with (BCells.shadow_addr (TRANS_STR_PC + 16)). exact (dn_const_vis _ _ _ _ _ _ _ HAR D6).
      + change 2147467795 with (BCells.shadow_addr (TRANS_STR_PC + 24)). exact (dn_const_vis _ _ _ _ _ _ _ HAR D7).
      + change 2147467796 with (BCells.shadow_addr TRANS_CMD). exact (dn_const_vis _ _ _ _ _ _ _ HAR CMD).
      + change 2147467797 with (BCells.shadow_addr (TRANS_CMD + 8)). exact (dn_const_vis _ _ _ _ _ _ _ HAR D8).
      + change 2147467798 with (BCells.shadow_addr (TRANS_CMD + 16)). exact (dn_const_vis _ _ _ _ _ _ _ HAR D9).
      + change 2147467799 with (BCells.shadow_addr (TRANS_CMD + 24)). exact (dn_const_vis _ _ _ _ _ _ _ HAR D10). }
  split; [destruct Hq as [-> | ->]; unfold amem_range, kLowMemEnd, TRANS_STR_C24, TRANS_STR_PC; lia|].
  destruct Hq as [-> | ->]; unfold TRANS_STR_C24, TRANS_STR_PC; lia.
Qed.

Lemma dn_stk : stk rsegs memc (spZ regs - DNAMED_STK) (spZ regs).
Proof.
  pose proof dn_sp_rng as [SP1 SP2]. pose proof asan_consts as (C1 & _).
  apply (decode_stk_present (w_H W)); [dn_lia | dn_lia|].
  intros a Ha. apply dn_pres. dn_lia.
Qed.

(* ---- the inner journal ---- *)

Lemma dn_inner : ajournalB DNAMED_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memc mdc 0.
Proof.
  pose proof dn_stk_ok as (Hal16 & _).
  apply (@ajournal_sub_init rc YE2k.tfib_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
           DNAMED_STK (spZ regs) [] (spZ regs - sp0) HJ);
    [lia | rewrite Zminus_mod, HAL, Hal16; reflexivity | lia | dn_lia | lia].
Qed.

(* The inner journal across one run: the run writes only its own frame [sp - 16, sp), which lies in the journal's
   stack window (YCbq.v ajournal_exec). *)
Lemma dn_journal_run : forall (mem1 mem2 : word -> option byte) (md1 md2 : Model),
  ajournalB DNAMED_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem1 md1 0 ->
  munch [(spZ regs - 16, spZ regs)] mem1 mem2 ->
  wmono rsegs mem1 mem2 ->
  same_but_materialized md1 md2 ->
  ajournalB DNAMED_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0.
Proof.
  intros mem1 mem2 md1 md2 JI MU WM SBM.
  pose proof dn_sp_rng as [SP1 SP2]. unfold DNAMED_STK, DNAMED_FRAME, ESTACK in *.
  pose proof asan_consts as (C1 & _).
  apply (@ajournal_exec rc YE2k.tfib_sink_head segs B LAWS decode_segs_low _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mem2 md2
           (fun a => spZ regs - 16 <= a < spZ regs) JI).
  - intros x Hx. unfold mrestrict. destruct (w_H W x) eqn:Eh; [reflexivity|].
    apply MU. cbn [outside]. split; [lia | exact I].
  - intros x Hx. unfold mrestrict in *. revert Hx. destruct (w_H W x) eqn:Ehx; intros Hx; [exact Hx|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 16)) as [Hl|Hl];
      [rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh|Hh];
      [|rewrite (MU x); [exact Hx | cbn [outside]; split; [lia | exact I]]].
    assert (Hw : wview rsegs mem2 x <> None).
    { refine (WM x _). unfold wview. destruct (mem1 x) as [b|] eqn:Em;
        [discriminate | exfalso; first [exact (Hx Em) | exact (Hx eq_refl)]]. }
    unfold wview in Hw. destruct (mem2 x) as [b|] eqn:Em1; [discriminate|]. exfalso.
    rewrite (find_segment_none rsegs (bv_unsigned x)) in Hw; [exact (Hw eq_refl)|].
    intros Him. pose proof (decode_segs_low _ Him) as Hlow. unfold kLowMemEnd in Hlow. lia.
  - intros x Hh.
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs - 16)) as [Hl|Hl];
      [apply (MU x); cbn [outside]; split; [lia | exact I]|].
    destruct (Z_lt_le_dec (bv_unsigned x) (spZ regs)) as [Hh2|Hh2];
      [|apply (MU x); cbn [outside]; split; [lia | exact I]].
    exfalso.
    assert (Hxr : sp0 - STK <= bv_unsigned x < sp0) by lia.
    pose proof (proj1 (dn_pres _ Hxr)) as Hhx. rewrite Z_to_bv_bv_unsigned in Hhx. congruence.
  - exact SBM.
  - intros a Ha. cbv beta in Ha. left. dn_lia.
Qed.

(* ---- the close: the inner journal and the caller's compose into the statement's post ---- *)

Lemma dn_close : forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model),
  ajournalB DNAMED_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
  aregs_preserved regs regs2 ->
  YK11.getr regs2 (Z_to_bv 5 10) = w64 r ->
  SRr segs W (mkCfg (@YK11.mkst fx regs2 (YK11.getr regs (Z_to_bv 5 1)) mem2 (YK11.seg_rom segs)) md2)
    (transport_dnamed_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).
Proof.
  intros regs2 mem2 md2 JI HP HA0.
  pose proof dn_mod as (EBw & _).
  apply SRr_ret. unfold transport_dnamed_post, decode_cg_post.
  exists lyc, Sc, regs2, mem2, md2, 0.
  split; [reflexivity|].
  split; [unfold DNAMED_EV; lia|].
  split.
  { pose proof (ajournal_sub_tok segs B LAWS decode_segs_low STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
                  DNAMED_STK (spZ regs) [] [] lyc Sc W mem2 md2 0 HJ JI HWLO HWHI
                  ltac:(intros a (rg & Hr & _); destruct Hr)) as J.
    cbn [app] in J. exact J. }
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { exact (acall_kept_of_journal segs B decode_segs_low DNAMED_STK (spZ regs) [] [] lyc Sc W memc mdc
             lyc Sc W mem2 md2 0 (fun _ => False) JI dn_AR
             ltac:(intros a (rg & Hr & _); destruct Hr)
             ltac:(intros bq mq i Hb _ _; exact Hb)
             sink_closed_nil). }
  split; [exact (mle_start MT Sc MTL)|].
  split; [exact HA0 | exact EBw].
Qed.

(* The registers the epilogue restores are the caller's (ra and s0 from the frame, sp from the arithmetic, the
   others untouched or kept by the bcmp wrapper). *)
Lemma dn_pres_ret : forall (spx x5 x6 x7 r10 r11 r12 r13 x14 x15 x16 x17 x28 x29 x30 x31 : word)
    (g3 g4 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 : word),
  bv_unsigned spx = spZ regs ->
  g3 = YK11.getr regs (Z_to_bv 5 3) -> g4 = YK11.getr regs (Z_to_bv 5 4) -> g9 = YK11.getr regs (Z_to_bv 5 9) ->
  g18 = YK11.getr regs (Z_to_bv 5 18) -> g19 = YK11.getr regs (Z_to_bv 5 19) ->
  g20 = YK11.getr regs (Z_to_bv 5 20) -> g21 = YK11.getr regs (Z_to_bv 5 21) ->
  g22 = YK11.getr regs (Z_to_bv 5 22) -> g23 = YK11.getr regs (Z_to_bv 5 23) ->
  g24 = YK11.getr regs (Z_to_bv 5 24) -> g25 = YK11.getr regs (Z_to_bv 5 25) ->
  g26 = YK11.getr regs (Z_to_bv 5 26) -> g27 = YK11.getr regs (Z_to_bv 5 27) ->
  aregs_preserved regs
    (mkR (YK11.getr regs (Z_to_bv 5 1)) spx g3 g4 x5 x6 x7 (YK11.getr regs (Z_to_bv 5 8)) g9 r10 r11 r12 r13
         x14 x15 x16 x17 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 x28 x29 x30 x31).
Proof.
  intros spx x5 x6 x7 r10 r11 r12 r13 x14 x15 x16 x17 x28 x29 x30 x31
    g3 g4 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27 Hsp E3 E4 E9 E18 E19 E20 E21 E22 E23 E24 E25 E26 E27 rr Hr.
  subst g3 g4 g9 g18 g19 g20 g21 g22 g23 g24 g25 g26 g27.
  unfold acallee_saved in Hr.
  assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst rr; try reflexivity.
  apply bv_eq. exact Hsp.
Qed.

(* The registers of a state ms_eqv to a concrete map. *)
Lemma dn_pres_eqv : forall (R F : bvmap 5 word) pc fc rv m ro ms',
  ms_eqv (MS R F pc fc rv m ro) ms' -> aregs_preserved regs R -> aregs_preserved regs (ms_regs ms').
Proof.
  intros R F pc fc rv m ro ms' EQV HP rr Hr. unfold acallee_saved in Hr.
  assert (Hc : rr = 2 \/ rr = 3 \/ rr = 4 \/ rr = 8 \/ rr = 9 \/ rr = 18 \/ rr = 19 \/ rr = 20 \/ rr = 21 \/
               rr = 22 \/ rr = 23 \/ rr = 24 \/ rr = 25 \/ rr = 26 \/ rr = 27) by lia.
  repeat (destruct Hc as [Hc|Hc]); subst rr;
    (rewrite (dn_ms_reg R F pc fc rv m ro ms' _ EQV));
    apply HP; unfold acallee_saved; lia.
Qed.

(* ---- one call of bcmp on the inner journal (YCbq.v aj_bcmp_at at the statement's abcmp_realizes) ---- *)

Lemma dn_bcmp : forall (regsT : bvmap 5 word) (memT : word -> option byte) (mdT : Model)
    (x y n : Z) (raw : word) (Q : world segs -> config -> Prop),
  ajournalB DNAMED_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W memT mdT 0 ->
  YK11.getr regsT (Z_to_bv 5 10) = w64 x -> YK11.getr regsT (Z_to_bv 5 11) = w64 y ->
  YK11.getr regsT (Z_to_bv 5 12) = w64 n ->
  0 <= n <= 8 ->
  decode_rd_ok W memT x n -> decode_rd_ok W memT y n ->
  (x + n <= spZ regs - DNAMED_STK \/ spZ regs <= x) ->
  (y + n <= spZ regs - DNAMED_STK \/ spZ regs <= y) ->
  YK11.getr regsT (Z_to_bv 5 2) = Z_to_bv 64 (spZ regs + -16) ->
  YK11.getr regsT (Z_to_bv 5 3) = w64 (as_gp B) -> YK11.getr regsT (Z_to_bv 5 4) = w64 (as_tp B) ->
  YK11.getr regsT (Z_to_bv 5 1) = raw -> YK0s.ret_ok raw ->
  (forall (regs2 : bvmap 5 word) (mem2 : word -> option byte) (md2 : Model) (v : word),
     ajournalB DNAMED_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem2 md2 0 ->
     aregs_preserved regsT regs2 -> YK11.getr regs2 (Z_to_bv 5 10) = v ->
     (v = w64 0 <-> forall i, 0 <= i < n -> aview segs (w_H W) memT (x + i) = aview segs (w_H W) memT (y + i)) ->
     (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - DNAMED_STK \/ spZ regs + -16 <= a) ->
        aview segs (w_H W) mem2 a = aview segs (w_H W) memT a) ->
     (forall a, apresent (w_H W) memT a -> apresent (w_H W) mem2 a) ->
     SRr segs W (mkCfg (@YK11.mkst fx regs2 raw mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W
    (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 (transportb_sigma TB___interceptor_trampoline_bcmp)) memT
              (YK11.seg_rom segs)) mdT) Q.
Proof.
  intros regsT memT mdT x y n raw Q JI R10 R11 R12 Hn RDX RDY OFX OFY R2 R3 R4 R1 HRAW K.
  pose proof dn_sp_rng as [SP1 SP2]. unfold DNAMED_STK, DNAMED_FRAME, ESTACK in *.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof RDX as (HvX & HraX & HhX & HmX & H0X & H63X).
  pose proof RDY as (HvY & HraY & HhY & HmY & H0Y & H63Y).
  assert (HspT : spZ regsT = spZ regs + -16)
    by (change (spZ regsT) with (bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)));
        rewrite R2; rewrite unsigned_lit; [reflexivity | lia]).
  eapply SRr_bind.
  { apply (@aj_bcmp_at fx rc YE2k.tfib_sink_head segs B LAWS decode_segs_low
             (transportb_sigma TB___interceptor_trampoline_bcmp) (ABCMPH fx) W regsT memT
             DNAMED_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc mdT 0 x y n (-16) raw JI).
    - exact R10.
    - exact R11.
    - exact R12.
    - lia.
    - exact H0X.
    - lia.
    - exact H0Y.
    - lia.
    - exact HspT.
    - reflexivity.
    - lia.
    - dn_lia.
    - exact R3.
    - exact R4.
    - exact R1.
    - exact HRAW.
    - intros a Ha. split; [exact (HvX a Ha)|]. rewrite HspT. unfold ESTACK. lia.
    - intros a Ha. split; [exact (HvY a Ha)|]. rewrite HspT. unfold ESTACK. lia.
    - intros a Ha. unfold ESTACK. lia.
    - intros a Ha. unfold ESTACK. lia.
    - exact HmX.
    - exact HmY.
    - exact HraX.
    - intros _. exact HhX.
    - exact HraY.
    - intros _. exact HhY. }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & v & -> & JI2 & HP2 & Hv & Hiff & Hview & Happ).
  apply (K regs2 mem2 md2 v JI2 HP2 Hv Hiff).
  - intros a Ha1 Ha2. apply Hview; [lia|]. unfold ESTACK. destruct Ha2; lia.
  - exact Happ.
Qed.

(* The frame the prologue wrote is kept by a call whose window lies below it. *)
Lemma dn_frame_call : forall (mem1 mem2 : word -> option byte) (md1 : Model) (cs : list cell),
  ajournalB DNAMED_STK (spZ regs) [] lyc Sc W memc mdc [] lyc Sc W mem1 md1 0 ->
  (forall a, 0 <= a < 2 ^ 64 -> (a + 1 <= spZ regs - DNAMED_STK \/ spZ regs + -16 <= a) ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) mem1 a) ->
  (forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem2 a) ->
  rw_cells rsegs mem1 (spZ regs + -16) cs -> Z.of_nat (cells_size cs) <= 16 ->
  rw_cells rsegs mem2 (spZ regs + -16) cs.
Proof.
  intros mem1 mem2 md1 cs JI Hview Happ FR Hsz.
  pose proof dn_sp_rng as [SP1 SP2]. unfold DNAMED_STK, DNAMED_FRAME, ESTACK in *.
  pose proof asan_consts as (C1 & _).
  pose proof JI as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HP & _).
  apply (decode_rw_cells_eq mem1 mem2 (spZ regs + -16) cs FR).
  intros i Hi.
  assert (Hp1 : apresent (w_H W) mem1 (spZ regs + -16 + i))
    by (apply HP; unfold DNAMED_STK, DNAMED_FRAME, ESTACK; lia).
  exact (decode_byte_eq (w_H W) (w_H W) mem1 mem2 (spZ regs + -16 + i) Hp1 (Happ _ Hp1)
           (Hview (spZ regs + -16 + i) ltac:(lia) ltac:(right; lia))).
Qed.

(* bcmp's test of [p + 24, p + 32) against a string q, at a memory whose view of the name is the entry state's:
   it is desk_named_m's test of the name against the string's bytes. *)
Lemma dn_cmp : forall (mT : word -> option byte) (q : Z) (NAME : list byte),
  (8 <= length (skipn 24 body))%nat -> length NAME = 8%nat ->
  (forall i, 0 <= i < 8 -> aview segs (w_H W) mT (p + 24 + i) = aview segs (w_H W) memc (p + 24 + i)) ->
  (forall i, 0 <= i < 8 ->
     aview segs (w_H W) mT (q + i) = Some (bv_unsigned (nth (Z.to_nat i) NAME (Z_to_bv 8 0)))) ->
  ((forall i, 0 <= i < 8 -> aview segs (w_H W) mT (p + 24 + i) = aview segs (w_H W) mT (q + i)) <->
   TWorld.zs (firstn 8 (skipn 24 body)) = TWorld.zs NAME).
Proof.
  intros mT q NAME L8 LN KB KQ. rewrite length_skipn in L8.
  apply (dn_cmp_iff (firstn 8 (skipn 24 body)) NAME (fun i => aview segs (w_H W) mT (p + 24 + i))
           (fun i => aview segs (w_H W) mT (q + i))).
  - rewrite length_firstn, length_skipn. lia.
  - exact LN.
  - intros i Hi. cbv beta. rewrite (KB i Hi). replace (p + 24 + i) with (p + (24 + i)) by lia.
    rewrite (dn_view_body (24 + i) ltac:(lia)). rewrite dn_nth_fs by lia.
    replace (Z.to_nat (24 + i)) with (24 + Z.to_nat i)%nat by lia. reflexivity.
  - intros i Hi. exact (KQ i Hi).
Qed.

(* ---- the walk ---- *)

Ltac dn_pres_rw HP :=
  rewrite (HP 2 ltac:(unfold acallee_saved; lia)), (HP 3 ltac:(unfold acallee_saved; lia)),
    (HP 4 ltac:(unfold acallee_saved; lia)), (HP 8 ltac:(unfold acallee_saved; lia)),
    (HP 9 ltac:(unfold acallee_saved; lia)), (HP 18 ltac:(unfold acallee_saved; lia)),
    (HP 19 ltac:(unfold acallee_saved; lia)), (HP 20 ltac:(unfold acallee_saved; lia)),
    (HP 21 ltac:(unfold acallee_saved; lia)), (HP 22 ltac:(unfold acallee_saved; lia)),
    (HP 23 ltac:(unfold acallee_saved; lia)), (HP 24 ltac:(unfold acallee_saved; lia)),
    (HP 25 ltac:(unfold acallee_saved; lia)), (HP 26 ltac:(unfold acallee_saved; lia)),
    (HP 27 ltac:(unfold acallee_saved; lia)).

Lemma dn_holds :
  SRr segs W (@cfg_at fx segs (transportb_sigma TB_desk_named) regs memc mdc)
    (transport_dnamed_post B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs Bw Bw' r).
Proof using All.
  pose proof dn_sp_rng as [SP1 SP2].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof dn_AR as HAR.
  pose proof dn_mod as (EBw & HL & Er).
  pose proof dn_len as Lb.
  pose proof dn_rdb as RDB.
  pose proof RDB as (RBv & RBra & RBh & RBm & RB0 & RB63).
  (* the body's shadow, in the run's form (TransportFevt.v decode_addressable_of) *)
  pose proof (decode_addressable_of (w_H W) memc p _ RBra RBm ltac:(lia) ltac:(lia)) as (AWB & HSV).
  assert (ESP : bv_unsigned (YK11.getr regs (Z_to_bv 5 2)) = spZ regs) by reflexivity.
  assert (GRET : ret_pc (YK11.getr regs (Z_to_bv 5 1)) = YK11.getr regs (Z_to_bv 5 1))
    by exact (LeafCgFacts.ret_ok_stmt_YK0s _ HRET).
  assert (G10 : YK11.getr regs (Z_to_bv 5 10) = w64 p) by exact H10.
  pose proof OWB as OWB'. unfold decode_off_win in OWB'.
  pose proof (decode_cells_asan B HCELLS lyc Sc W memc mdc HAR) as (CK & GCK & _).
  assert (RDC : decode_rd_ok W memc TRANS_STR_C24 8).
  { apply dn_str_rd; [left; reflexivity|]. intros i Hi. rewrite (dn_view_c24 i Hi). discriminate. }
  assert (RDP : decode_rd_ok W memc TRANS_STR_PC 8).
  { apply dn_str_rd; [right; reflexivity|]. intros i Hi. rewrite (dn_view_pc i Hi). discriminate. }
  (* ---- the first run: the entry to the first call, or to the return ---- *)
  eapply decode_run.
  { unfold LCK.ms_of_regs. rewrite G10.
    eapply DNRun.dn_run1_F with (lo := spZ regs - DNAMED_STK) (body := body).
    - exact HP0.
    - exact RB63.
    - exact dn_bytes.
    - exact HL.
    - exact dn_stk.
    - dn_lia.
    - exact CK.
    - exact GCK.
    - unfold FC.app_mem, FC.LOWMEM_END, FC.HIGHMEM_BEG, FC.APPMEM_END. dn_lia.
    - unfold FC.app_mem, FC.LOWMEM_END, FC.HIGHMEM_BEG, FC.APPMEM_END. dn_lia.
    - unfold AsanKA.off_stk, FC.GOT_CELL_K. dn_lia.
    - unfold AsanKA.off_stk, FC.CELL_K. dn_lia.
    - unfold AsanKA.off_stk. dn_lia.
    - exact AWB.
    - apply decode_rng_vis; [dn_lia | dn_lia |]. intros i Hi.
      exact (proj1 (dn_pres (spZ regs - 16 + i) ltac:(dn_lia))).
    - exact (CgBNoTwin.cgb_cell_rng W FC.GOT_CELL_K 8 ltac:(vm_compute; reflexivity)
               ltac:(unfold FC.GOT_CELL_K; lia)).
    - exact (CgBNoTwin.cgb_cell_rng W FC.CELL_K 8 ltac:(vm_compute; reflexivity) ltac:(unfold FC.CELL_K; lia)).
    - intros i Hi.
      pose proof (decode_shadow_high (p + i) ltac:(unfold amem_range in RBm; lia)) as SH.
      apply decode_rng_vis; [lia | lia |]. intros j Hj.
      replace (FC.shadow_addr (p + i) + j) with (FC.shadow_addr (p + i)) by lia. exact (HSV i Hi).
    - apply decode_rng_vis; [lia | lia|]. intros j Hj.
      destruct (aview segs (w_H W) memc (p + j)) as [v|] eqn:Ev; [exact (dn_aview_vis W memc _ v Ev)|].
      exfalso. exact (RBv (p + j) ltac:(lia) Ev). }
  intros ms0 ms' md' POST EQV _ SBM.
  unfold DNRun.dn_post1 in POST.
  destruct POST as (m1 & MU & WM & [(N8 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & spx & -> & Hsp & Ha0)
                                  | (N8 & FR & r1 & r2 & r8 & r10 & r11 & r12 & r13 & r14 & r15 & r16 & -> &
                                     E1 & E2 & E8 & E10 & E11 & E12)]).
  - (* ---- a name of another length: a0 = 0 ---- *)
    rewrite (dn_ms_shape _ _ _ _ EQV). rewrite GRET.
    apply (dn_close (ms_regs ms') m1 md').
    + exact (dn_journal_run memc m1 mdc md' dn_inner MU WM SBM).
    + apply (dn_pres_eqv _ _ _ _ _ _ _ _ EQV). apply dn_pres_ret; [exact Hsp | reflexivity ..].
    + rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV).
      transitivity r10; [reflexivity|]. apply bv_eq. rewrite Ha0, Er, dn_r_ne8 by exact N8. reflexivity.
  - (* ---- a name of 8 bytes: the first call of bcmp, against CNTRL|24 ---- *)
    rewrite (dn_ms_shape _ _ _ _ EQV).
    pose proof (dn_journal_run memc m1 mdc md' dn_inner MU WM SBM) as JI1.
    assert (L33 : 33 <= Z.of_nat (length body)).
    { pose proof HL as HL'. rewrite N8, length_skipn in HL'. lia. }
    (* the views the prologue keeps *)
    assert (KV1 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - 16 <= a < spZ regs) ->
      aview segs (w_H W) m1 a = aview segs (w_H W) memc a).
    { intros a Ha Hn. apply aview_eq_of. unfold mrestrict. destruct (w_H W (Z_to_bv 64 a)); [reflexivity|].
      apply MU. cbn [outside]. rewrite unsigned_lit by lia. split; [lia | exact I]. }
    pose proof (dn_rd_keep W memc m1 p _ (spZ regs - 16) (spZ regs) RDB ltac:(lia) ltac:(dn_lia) ltac:(dn_lia) KV1)
      as RDB1.
    pose proof (dn_rd_keep W memc m1 TRANS_STR_C24 8 (spZ regs - 16) (spZ regs) RDC ltac:(lia) ltac:(dn_lia)
                  ltac:(left; unfold TRANS_STR_C24; dn_lia) KV1) as RDC1.
    pose proof (dn_rd_keep W memc m1 TRANS_STR_PC 8 (spZ regs - 16) (spZ regs) RDP ltac:(lia) ltac:(dn_lia)
                  ltac:(left; unfold TRANS_STR_PC; dn_lia) KV1) as RDP1.
    eapply (dn_bcmp (ms_regs ms') m1 md' (p + 24) TRANS_STR_C24 8 (Z_to_bv 64 DNRun.DN_RET1)).
    + exact JI1.
    + rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV).
      transitivity r10; [reflexivity|]. apply bv_eq. rewrite E10. unfold w64. rewrite unsigned_lit by lia.
      reflexivity.
    + rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV).
      transitivity r11; [reflexivity|]. apply bv_eq. rewrite E11. reflexivity.
    + rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV).
      transitivity r12; [reflexivity|]. apply bv_eq. rewrite E12. reflexivity.
    + lia.
    + exact (trans_rd_ok_sub W m1 p _ (p + 24) 8 RDB1 ltac:(lia) ltac:(lia) ltac:(lia)).
    + exact RDC1.
    + dn_lia.
    + unfold TRANS_STR_C24. dn_lia.
    + rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV).
      transitivity r2; [reflexivity|]. apply bv_eq. rewrite E2, unsigned_lit by dn_lia. lia.
    + rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV). exact HGP.
    + rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV). exact HTP.
    + rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV). transitivity r1; [reflexivity | exact E1].
    + apply YK0s.ret_ok_even. vm_compute. reflexivity.
    + intros regs2 mem2 md2 v JI2 HP2 Hv Hiff Hview Happ.
      pose proof (dn_frame_call m1 mem2 md' _ JI1 Hview Happ FR ltac:(cbn [cells_size csize]; lia)) as FR2.
      assert (KV2 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - DNAMED_STK <= a < spZ regs - 16) ->
        aview segs (w_H W) mem2 a = aview segs (w_H W) m1 a).
      { intros a Ha Hn. apply Hview; [exact Ha | dn_lia]. }
      (* bcmp's answer: the name against CNTRL|24 *)
      assert (CMP1 : v = w64 0 <-> TWorld.zs (firstn 8 (skipn 24 body)) = TWorld.zs TC.C24_NAME).
      { etransitivity; [exact Hiff|]. apply dn_cmp; [rewrite length_skipn; lia | reflexivity | |].
        + intros i Hi. apply KV1; [lia | dn_lia].
        + intros i Hi.
          rewrite (KV1 (TRANS_STR_C24 + i) ltac:(unfold TRANS_STR_C24; lia) ltac:(unfold TRANS_STR_C24; dn_lia)).
          exact (dn_view_c24 i Hi). }
      pose proof JI2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR2 & _).
      (* ---- the second run: the first call's return ---- *)
      eapply decode_run.
      { unfold LCK.ms_of_regs. dn_pres_rw HP2. rewrite Hv.
        rewrite !(dn_ms_reg _ _ _ _ _ _ _ _ _ EQV).
        eapply DNRun.dn_run2_F with (sp2 := r2) (x8 := r8).
        + dn_lia.
        + dn_lia.
        + replace (bv_unsigned r2) with (spZ regs + -16) by lia. exact FR2.
        + rewrite E2. apply decode_rng_vis; [dn_lia | dn_lia|]. intros i Hi.
          exact (proj1 (HPR2 (spZ regs - 16 + i) ltac:(dn_lia))). }
      intros ms20 ms2 md2' POST2 EQV2 _ SBM2.
      destruct POST2 as [(Ev & r10' & spx & -> & Hsp & Ha0)
                        | (Nv & r1' & r10' & r11' & r12' & -> & E1' & E10' & E11' & E12')].
      * (* bcmp answered 0: the name is CNTRL|24, a0 = SPEC_C24 *)
        rewrite (dn_ms_shape _ _ _ _ EQV2). rewrite GRET.
        apply (dn_close (ms_regs ms2) mem2 md2').
        -- exact (dn_journal_run mem2 mem2 md2 md2' JI2 (munch_refl _ _) (wmono_refl rsegs mem2) SBM2).
        -- apply (dn_pres_eqv _ _ _ _ _ _ _ _ EQV2). apply dn_pres_ret; [|reflexivity ..].
           rewrite Hsp, E2. lia.
        -- rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV2).
           transitivity r10'; [reflexivity|]. apply bv_eq. rewrite Ha0, Er, N8, dn_r_c24; [reflexivity|].
           apply CMP1. exact Ev.
      * (* bcmp did not answer 0: the second call, against MAINUNIT *)
        rewrite (dn_ms_shape _ _ _ _ EQV2).
        pose proof (dn_journal_run mem2 mem2 md2 md2' JI2 (munch_refl _ _) (wmono_refl rsegs mem2) SBM2) as JI2'.
        assert (NC24 : TWorld.zs (firstn 8 (skipn 24 body)) <> TWorld.zs TC.C24_NAME)
          by (intros E; apply Nv; apply CMP1; exact E).
        pose proof (dn_rd_keep W m1 mem2 p _ (spZ regs - DNAMED_STK) (spZ regs - 16) RDB1 ltac:(lia)
                      ltac:(dn_lia) ltac:(dn_lia) KV2) as RDB2.
        pose proof (dn_rd_keep W m1 mem2 TRANS_STR_PC 8 (spZ regs - DNAMED_STK) (spZ regs - 16) RDP1 ltac:(lia)
                      ltac:(dn_lia) ltac:(left; unfold TRANS_STR_PC; dn_lia) KV2) as RDP2.
        eapply (dn_bcmp (ms_regs ms2) mem2 md2' (p + 24) TRANS_STR_PC 8 (Z_to_bv 64 DNRun.DN_RET2)).
        -- exact JI2'.
        -- rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV2).
           transitivity r10'; [reflexivity|]. apply bv_eq. rewrite E10', E8. unfold w64.
           rewrite unsigned_lit by lia. reflexivity.
        -- rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV2).
           transitivity r11'; [reflexivity|]. apply bv_eq. rewrite E11'. reflexivity.
        -- rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV2).
           transitivity r12'; [reflexivity|]. apply bv_eq. rewrite E12'. reflexivity.
        -- lia.
        -- exact (trans_rd_ok_sub W mem2 p _ (p + 24) 8 RDB2 ltac:(lia) ltac:(lia) ltac:(lia)).
        -- exact RDP2.
        -- dn_lia.
        -- unfold TRANS_STR_PC. dn_lia.
        -- rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV2).
           transitivity r2; [reflexivity|]. apply bv_eq. rewrite E2, unsigned_lit by dn_lia. lia.
        -- rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV2). exact HGP.
        -- rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV2). exact HTP.
        -- rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV2).
           transitivity r1'; [reflexivity | exact E1'].
        -- apply YK0s.ret_ok_even. vm_compute. reflexivity.
        -- intros regs3 mem3 md3 w JI3 HP3 Hw Hiff2 Hview2 Happ2.
           pose proof (dn_frame_call mem2 mem3 md2' _ JI2' Hview2 Happ2 FR2 ltac:(cbn [cells_size csize]; lia))
             as FR3.
           (* bcmp's answer: the name against MAINUNIT *)
           assert (CMP2 : w = w64 0 <-> TWorld.zs (firstn 8 (skipn 24 body)) = TWorld.zs TC.PC_NAME).
           { etransitivity; [exact Hiff2|]. apply dn_cmp; [rewrite length_skipn; lia | reflexivity | |].
             + intros i Hi. rewrite (KV2 (p + 24 + i) ltac:(lia) ltac:(dn_lia)). apply KV1; [lia | dn_lia].
             + intros i Hi.
               rewrite (KV2 (TRANS_STR_PC + i) ltac:(unfold TRANS_STR_PC; lia) ltac:(unfold TRANS_STR_PC; dn_lia)).
               rewrite (KV1 (TRANS_STR_PC + i) ltac:(unfold TRANS_STR_PC; lia) ltac:(unfold TRANS_STR_PC; dn_lia)).
               exact (dn_view_pc i Hi). }
           pose proof JI3 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR3 & _).
           (* ---- the third run: the second call's return ---- *)
           eapply decode_run.
           { unfold LCK.ms_of_regs. dn_pres_rw HP3. rewrite Hw.
             rewrite !(dn_ms_reg _ _ _ _ _ _ _ _ _ EQV2).
             eapply DNRun.dn_run3_F with (sp2 := r2).
             + dn_lia.
             + dn_lia.
             + replace (bv_unsigned r2) with (spZ regs + -16) by lia. exact FR3.
             + rewrite E2. apply decode_rng_vis; [dn_lia | dn_lia|]. intros i Hi.
               exact (proj1 (HPR3 (spZ regs - 16 + i) ltac:(dn_lia))). }
           intros ms30 ms3 md3' POST3 EQV3 _ SBM3.
           destruct POST3 as (r10'' & spx & -> & Hsp & HW).
           rewrite (dn_ms_shape _ _ _ _ EQV3). rewrite GRET.
           apply (dn_close (ms_regs ms3) mem3 md3').
           ++ exact (dn_journal_run mem3 mem3 md3 md3' JI3 (munch_refl _ _) (wmono_refl rsegs mem3) SBM3).
           ++ apply (dn_pres_eqv _ _ _ _ _ _ _ _ EQV3). apply dn_pres_ret; [|reflexivity ..].
              rewrite Hsp, E2. lia.
           ++ rewrite (dn_ms_reg _ _ _ _ _ _ _ _ _ EQV3).
              transitivity r10''; [reflexivity|]. apply bv_eq.
              destruct HW as [(Ew & Ha0) | (Nw & Ha0)]; rewrite Ha0, Er, N8.
              ** rewrite dn_r_pc; [reflexivity | exact NC24 | apply CMP2; exact Ew].
              ** rewrite dn_r_none; [reflexivity | exact NC24 | intros E; apply Nw; apply CMP2; exact E].
Qed.

End Call.
End Walk.

(* The statement of lib/B/Prog/desk_named_cg.v: the runtime cells, the strings' guard cells, the allocator and meter
   laws and the bcmp contract give the contract at TB_desk_named. *)
Theorem transport_desk_named_cg_holds {fx : YK11.FPState} {rc : YM05.RunCeil} (B : asyms) (MT : ameter_ops) :
  @transport_desk_named_cg_holds_stmt fx rc B MT.
Proof.
  intros HCELLS HDNC HOWN HERR LAWS MTL ABCMP.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p r body Bw Bw'.
  intros HJ HRET HRA4 HGP HTP H10 HAL HWLO HWHI HP0 GBB HSRC OWB HROM HM HNEV.
  exact (dn_holds B MT HCELLS HDNC LAWS MTL ABCMP STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs
           p r body Bw Bw' HJ HRET HRA4 HGP HTP H10 HAL HWLO HWHI HP0 GBB HSRC OWB HROM HM HNEV).
Qed.

Print Assumptions transport_desk_named_cg_holds.
