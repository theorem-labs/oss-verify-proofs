(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported from proofs/cgif/cgif_file_fuzzer/lib/A/AFip.v (segA: the run of a
   wrapper over its own instruction table, the application of a runtime-entry contract at a call site and the
   rebuilding of the symbolic state after the call), A/AFis.v (at_ST's frame and window conjuncts,
   kept_of_frame, chunk_val_at) and A/AF0x.v (st_ok_pin_reg, the val_mem / apresent / fpchain helpers) to
   libreac/fuzz_decode's calloc wrapper in image A (fuzz_decode.asan); module paths changed, and every address,
   cell and offset below is decode's own. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_decode/lib/A/DecodeCallocWrap.v, with its module paths and module names changed; 3365 of its 3449 lines of code are new or changed and 788 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/LLVMFuzzerTestOneInput_seg_cfg.v, with its module names changed; 687 of its 783 lines of code are new or changed and 3353 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4sys: Lemma lc_op4sys_ok : lc_op4sys_stmt of
   lib/B/Prog/LLVMFuzzerTestOneInput_segs.v, one turn of op 4's spec_system_at loop over c (the struct diginet_cmd at
   F + 32) in fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput (image B), +0x10b0 .. +0x1158 and +0x1164 .. +0x116c,
   from the cut SYSL(i) to SYSL(i + 1) or SYSJ. The port of image A's lib/A/Prog/LLVMFuzzerTestOneInput_seg_op4sys.v.

   The code (an offset +X is the address 0x812a0 + X; at SYSL a2 = len, a3 = i + 3, s4 = c, s6 = 3, s9 = 0xf0,
   s10 = the shadow base, 160(s1) = 2 ^ 64 - 1 - c and 176(s1) = c + 1, lf_spill_loop):
     +0x10b0  add a0,s4,a3 ; beq a0,s6,+0x1b44                                a0 = c + i + 3; UBSan: c + i null
     +0x10b8  addi a1,a0,-3 ; srli / add / lb a4 ; bnez a4,+0x1138           the check of c[i]
     +0x10cc  ld a5,176(s1) ; add a5,a5,a3 ; lbu a1,-4(a5) ; bne a1,s9,+0x112c c[i] = 0xf0 ?
     +0x10dc  addi a4,a3,-3 ; ld a1,160(s1) ; bgeu a4,a1,+0x1b44             UBSan: c + i + 1
     +0x10e8  addi a1,a0,-2 ; srli / add / lb a6 ; bnez a6,+0x1144           the check of c[i + 1]
     +0x10fc  lbu a1,-3(a5) ; li a6,0x13 ; bne a1,a6,+0x112c                 c[i + 1] = 0x13 ?
     +0x1108  ld a1,160(s1) ; bltu a1,a3,+0x1b44                             UBSan: c + i + 3
     +0x1110  srli / add / lb a1 ; bnez a1,+0x1150                           the check of c[i + 3]
     +0x1120  lbu a0,-1(a5) ; li a1,0x70 ; beq a0,a1,+0x1168                 c[i + 3] = 0x70 ?
     +0x112c  addi a3,a3,1 ; bne a2,a3,+0x10b0 ; j +0x1164                    the next turn
     +0x1164  li a4,-1 ; +0x1168 slti a0,a4,0 ; +0x116c xori t2,a0,1          then SYSJ (+0x1170)
   The slow paths +0x1138 / +0x1144 / +0x1150 (`andi`, `blt` back to the load, `j` to the report stubs
   +0x1c3c .. +0x1c4c: the __asan_report_load1 calls 0x82ee0, 0x82ee8, 0x82eec) are not reached: the three bytes lie in
   c, whose four shadow bytes are 0 while op 4 runs (lc_fsh .. true false), so the token engine reads each check's
   shadow byte from that granule (sy_ra, shent_ok_of_range) and leaves no obligation. The three branches to the UBSan
   trap word +0x1b44 (trap edges 0x82354, 0x82384, 0x823ac) are decided by the engine from the seat's facts: a0 is
   the atom 32 = c + i + 3 in [4096, 2 ^ 47) and s6 = 3, so `beq a0, s6` is not taken; a4 = i in [0, 20] and
   160(s1) = 2 ^ 64 - 1 - c >= 2 ^ 64 - 2 ^ 47, so neither `bgeu a4, a1` nor `bltu a1, a3` (a3 = i + 3 <= 23) is taken.

   How it is proved. Two seats, both over the caller's G journal (lib/B/Prog/TransportGRunB.v paj_run_x /
   paj_run_to_x, G_HARNESS_B, no out window):
     sy_ss at +0x10b0: every register an atom; atom 32 = c + i + 3 with the alias fact s4 + a3 = atom 32, so the
       engine names both `add a0, s4, a3` (atom 32) and `add a5, a5, a3` (176(s1) = s4 + 1, atom 32 + 1) by it; the
       read-only region of the three bytes c[i], c[i + 1], c[i + 3] at atom 32 - 3, - 2, + 0 (atoms 33, 34, 35); the
       read-only region of the spill slots 160(s1) (atom 36) and 176(s1) (s4 + 1); the shadow entry of [c + i, c + i
       + 4). Runs and branches up to +0x112c (a miss at i: the state sy_sysn), or to +0x1170 through the `beq` (a
       hit: SYSJ with t2 = 1).
     sy_ss0 at +0x112c (sy_tail): every register an atom, no region. The increment and `bne a2, a3`: back to +0x10b0
       (SYSL(i + 1)) or, at the last turn, through +0x1164 .. +0x116c to +0x1170 (SYSJ with t2 = 0).
   Every region is read-only, so the memory after each run is the memory before at every address (the frame of the
   run), the journal is the run's, and every fact of lc_tag_common carries over (sy_tag_kept). The model: the bytes
   the loads read are at8 of firstn len cbytes (c's 24 bytes are cbytes, sy_cb_len), so a miss at i is
   sys_hit .. i = false and a hit is system_at = true (DgnSpec.system_at_true); after the last turn every position
   below len - 3 missed, which is system_at = false (DgnSpec.system_at_false). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
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
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib YC1g CanKit.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg TransportGRwB TransportGRunB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
LLVMFuzzerTestOneInput_cg LLVMFuzzerTestOneInput_segs LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.


(* ------------------------------------------------------------------ *)
(* 1. The two seats                                                     *)
(* ------------------------------------------------------------------ *)

(* +0x112c, the increment after a miss at i. *)
Definition LO_SYSN : Z := 0x112c.
(* +0x10b0, turn i: atom 32 = c + i + 3 (a0 from +0x10b4 on); the read-only region of c[i], c[i + 1] and c[i + 3]
   at atom 32 - 3, - 2 and + 0 (atoms 33, 34, 35); the read-only spill slots 160(s1) (atom 36, 2 ^ 64 - 1 - c) and
   176(s1) (c + 1, the atom of s4 plus 1); s10 (atom 26) is the shadow base. The alias s4 + a3 = atom 32 names a0
   (+0x10b0) and a5 (+0x10d0, s4 + 1 + a3) by atom 32. *)
Definition sy_rg_c : YP09.region :=
  YP09.mkRegion (Some 32%nat) (-3) 1 0 0
    [YP09.mkChunk (-3) (CVal 1 (SOff 33 0)); YP09.mkChunk (-2) (CVal 1 (SOff 34 0));
     YP09.mkChunk 0 (CVal 1 (SOff 35 0))].
Definition sy_rg_s : YP09.region :=
  YP09.mkRegion (Some 9%nat) 160 184 0 0
    [YP09.mkChunk 160 (CVal 8 (SOff 36 0)); YP09.mkChunk 176 (CVal 8 (SOff 20 1))].
Definition sy_facts : facts :=
  mkFacts [(26%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, YC4b.PTR 0); (13%nat, mkAF 3 23 0);
           (22%nat, mkAF 3 3 0); (36%nat, mkAF (2 ^ 64 - 2 ^ 47) (2 ^ 64 - 1) 0);
           (33%nat, mkAF 0 255 0); (34%nat, mkAF 0 255 0); (35%nat, mkAF 0 255 0)] []
    [(SAlu ALU_ADD (SOff 20 0) (SOff 13 0), SOff 32 0)].
Definition sy_ss : sstate := mkSS LO_SYSL sr_atoms [sy_rg_c; sy_rg_s] None sy_facts.
Definition SY_SH : list shent := [mkSHE 32 (-3) 1].
Definition SY_Bx : sv := SOff 26 0.
(* A seat with every register an atom and no region. *)
Definition sy_ss0 (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).
Definition SY_B0 : Z * Z := (0, 0).

(* ------------------------------------------------------------------ *)
(* 2. The bytes of c and the model                                      *)
(* ------------------------------------------------------------------ *)

Lemma sy_nth_zs : forall (l : list byte) (j : nat), nth j (TW.zs l) 0 = DSpec.at8 l j.
Proof.
intros l j. unfold TW.zs, DSpec.at8, DSpec.bz.
exact (map_nth (fun b : byte => bv_unsigned b) l (DSpec.b8 0) j).
Qed.

(* The cursor before the len byte is in range: the op byte and the three key / display bytes keep it so. *)
Lemma sy_kd_ok : forall D c, QF.fuzz_in_ok D c -> QF.fuzz_in_ok D (sv_c (lc_sub_kd D (lc_oc D c))).
Proof.
intros D c Hc. unfold lc_oc.
destruct (QF.fuzz_u8_ok D c Hc) as (c1 & v1 & E1 & H1 & _). rewrite E1. cbn [fst].
unfold lc_sub_kd.
destruct (QF.fuzz_u8_ok D c1 H1) as (c2 & v2 & E2 & H2 & _). rewrite E2. cbv beta iota zeta.
destruct (QF.fuzz_u8_ok D c2 H2) as (c3 & v3 & E3 & H3 & _). rewrite E3. cbv beta iota zeta.
destruct (QF.fuzz_u8_ok D c3 H3) as (c4 & v4 & E4 & H4 & _). rewrite E4. cbv beta iota zeta.
exact H4.
Qed.

(* c's first 24 bytes are cbytes (the take stays inside the input), and 3 <= len <= 24. *)
Lemma sy_cb_len : forall D B1 c3, QF.fuzz_in_ok D c3 ->
  length (tg_cbytes (lc_tag_vals D B1 c3)) = 24%nat /\ 3 <= tg_len (lc_tag_vals D B1 c3) <= 24.
Proof.
intros D B1 c3 Hc. unfold lc_tag_vals.
destruct (QF.fuzz_u8_ok D c3 Hc) as (c4 & lb & E4 & H4 & Hlb). rewrite E4. cbv beta iota zeta.
pose proof (Z.mod_pos_bound lb 22 ltac:(lia)) as Hm.
destruct (QF.fuzz_take_ok D c4 (lb mod 22 + 3 - 3) H4 ltac:(lia)) as (c5 & off & n & E5 & _ & Hn & Hoff & Hend & _).
rewrite E5. cbv beta iota zeta. cbn [tg_cbytes tg_len].
split; [|lia].
rewrite !length_app, repeat_length. cbn [length].
rewrite QF.length_sub_D by lia. lia.
Qed.

(* The byte of c at j < len, as the memory holds it, is at8 of the spec's view firstn len cbytes. *)
Lemma sy_c_byte : forall (cb : list byte) len d key (j : nat), length cb = 24%nat -> len <= 24 ->
  (j < Z.to_nat len)%nat ->
  nth j (TW.zs (TOP.cmd_struct cb len d key)) 0 = DSpec.at8 (firstn (Z.to_nat len) cb) j.
Proof.
intros cb len d key j Hl Hlen Hj. rewrite sy_nth_zs. unfold TOP.cmd_struct.
rewrite DSpec.at8_app_l by lia. rewrite DSpec.at8_firstn by lia. reflexivity.
Qed.

Lemma sy_c_len : forall (cb : list byte) len d key, length cb = 24%nat ->
  length (TW.zs (TOP.cmd_struct cb len d key)) = 32%nat.
Proof.
intros cb len d key Hl. unfold TW.zs, TOP.cmd_struct. rewrite length_map, !length_app, Hl. reflexivity.
Qed.

(* c's 32 bytes are addressable: their four shadow bytes are 0 while op 4 runs. *)
Lemma sy_ra : forall (cx : lcx) (r : reader), lc_fsh cx r true false -> lc_F cx mod 64 = 0 -> 0 <= lc_F cx ->
  forall a n, lc_F cx + 32 <= a -> a + n <= lc_F cx + 64 -> range_addressable r SHADOW_OFF a n.
Proof.
intros cx r Hsh HF64 HF0 a n Ha Hn x Hx. exists 0. split; [|left; reflexivity].
unfold shadow_of_addr.
assert (Hq : lc_F cx = 64 * (lc_F cx / 64)) by (pose proof (Z.div_mod (lc_F cx) 64 ltac:(lia)); lia).
assert (HF8 : lc_F cx / 8 = 8 * (lc_F cx / 64)).
{ rewrite Hq at 1. replace (64 * (lc_F cx / 64)) with (8 * (lc_F cx / 64) * 8) by lia.
  apply Z.div_mul. lia. }
pose proof (Z.div_mod x 8 ltac:(lia)) as D8. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as M8.
assert (Hj : 4 <= x / 8 - lc_F cx / 8 < 8) by lia.
pose proof (Hsh (x / 8 - lc_F cx / 8) ltac:(lia)) as H.
unfold lc_SH in H. replace (SHADOW_OFF + lc_F cx / 8 + (x / 8 - lc_F cx / 8)) with (SHADOW_OFF + x / 8) in H by lia.
rewrite H. f_equal.
assert (E : x / 8 - lc_F cx / 8 = 4 \/ x / 8 - lc_F cx / 8 = 5 \/ x / 8 - lc_F cx / 8 = 6 \/
            x / 8 - lc_F cx / 8 = 7) by lia.
destruct E as [E | [E | [E | E]]]; rewrite E; reflexivity.
Qed.

(* A run whose regions are all read-only leaves the memory it read. *)
Lemma sy_frame_ro : forall E (rs : smem) (m m' : word -> option byte),
  forallb (fun r => YP09.r_whi r <=? YP09.r_wlo r) rs = true -> frame_of E rs m m' -> forall x, m' x = m x.
Proof.
intros E rs m m' Hro HF x. apply HF. intros (r & Hin & Hr).
rewrite forallb_forall in Hro. specialize (Hro r Hin). apply Z.leb_le in Hro. lia.
Qed.

(* A byte present before is present after a stretch that keeps the restricted memory. *)
Lemma sy_present : forall (H : word -> bool) (m m2 : word -> option byte),
  (forall x, mrestrict H m2 x = mrestrict H m x) -> forall a, apresent H m a -> apresent H m2 a.
Proof.
intros H m m2 K a (Hh & b & Hb). split; [exact Hh|]. exists b.
pose proof (K (Z_to_bv 64 a)) as E. unfold mrestrict in E. rewrite Hh in E. rewrite E. exact Hb.
Qed.

Ltac sy_in := cbn [In]; repeat (first [left; reflexivity | right]).

Ltac sy_md :=
  lazymatch goal with |- SRr _ _ (mkCfg _ ?mdx) _ =>
    let mdv := fresh "mdv" in set (mdv := mdx) in *; clearbody mdv end.
Ltac sy_km HFr KM :=
  lazymatch type of HFr with frame_of ?Ex ?rs ?m0 ?m1 =>
    pose proof (sy_frame_ro Ex rs m0 m1 ltac:(vm_compute; reflexivity) HFr) as KM end.
Ltac sy_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat (apply awr_ok_x_cons;
          [let x := fresh "x" in let Hx := fresh "Hx" in
           intros x Hx; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hx; lia |]);
  apply awr_ok_x_nil.

(* The value of register r of the machine state of a symbolic state, from its symbolic value. *)
Ltac sy_reg_at HS r v H tac :=
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict ?Hh ?msx) =>
    let e := eval vm_compute in (sr_get (ss_regs ssx) r) in
    assert (H : YK11.getr (ms_regs msx) r = v) by
      (refine (eq_trans (st_ok_pi_restrict_reg Hh Ex ssx msx r HS) _); change (sv_denot Ex e = v); tac)
  end.

(* ------------------------------------------------------------------ *)
(* 3. The walk's own section                                            *)
(* ------------------------------------------------------------------ *)

Section sy. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The walk's valuation at the head of turn i: the 32 registers, then atom 32 = c + i + 3, the three bytes and
   2 ^ 64 - 1 - c. *)
Definition sy_E (regs : bvmap 5 word) (a b0 b1 b3 q : Z) : env :=
  Eimg (PI := PI_transportb) (Ereg regs [w64 a; w64 b0; w64 b1; w64 b3; w64 q]).
Definition sy_E0 (regs : bvmap 5 word) : env := Eimg (PI := PI_transportb) (Ereg regs []).

Section fx. Context {fx : YK11.FPState}.

(* The seat at the head of turn i, c = s4 and k = a3 = i + 3. *)
Lemma sy_entry : forall (W : world segs) regs mem (c k s a b0 b1 b3 q : Z),
  YK11.getr regs 20 = w64 c -> YK11.getr regs 13 = w64 k -> YK11.getr regs 9 = w64 s ->
  YK11.getr regs 26 = w64 SHADOW_OFF -> YK11.getr regs 22 = w64 3 ->
  a = c + k -> q = 2 ^ 64 - 1 - c -> 3 <= k <= 23 -> 4099 <= a <= 140737479966720 -> 0 <= c -> c + 1 <= 2 ^ 47 ->
  0 <= s -> s + 184 <= 2 ^ 64 -> a + 1 <= s + 160 ->
  val_mem segs (mrestrict (w_H W) mem) (a - 3) 1 b0 -> val_mem segs (mrestrict (w_H W) mem) (a - 2) 1 b1 ->
  val_mem segs (mrestrict (w_H W) mem) a 1 b3 ->
  val_mem segs (mrestrict (w_H W) mem) (s + 160) 8 q -> val_mem segs (mrestrict (w_H W) mem) (s + 176) 8 (c + 1) ->
  0 <= b0 < 256 -> 0 <= b1 < 256 -> 0 <= b3 < 256 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (a - 3) 4 ->
  (forall x, a - 3 <= x < a + 1 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)) ->
  st_ok_pi segs VAL (sy_E regs a b0 b1 b3 q) sy_ss
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + LO_SYSL)) mem (YK11.seg_rom segs))) /\
  sh_ok segs SY_Bx SY_SH (sy_E regs a b0 b1 b3 q) (mrestrict (w_H W) mem).
Proof.
intros W regs mem c k s a b0 b1 b3 q R20 R13 R9 R26 R22 Ea Eq Hk Ha Hc0 Hc1 Hs0 Hs1 Hsa V0 V1 V3 VQ VC
  Hb0 Hb1 Hb3 Hra Happ.
set (E := sy_E regs a b0 b1 b3 q).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = YK11.getr regs r)
  by (intros n r Hn; unfold E, sy_E; apply can_ew_Eimg_Ereg_nat; exact Hn).
assert (EX : forall j, (j < 5)%nat -> ew E (32 + j) = nth j [w64 a; w64 b0; w64 b1; w64 b3; w64 q] (Z_to_bv 64 0))
  by (intros j Hj; unfold E, sy_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 0%nat ltac:(lia)) as E32. pose proof (EX 1%nat ltac:(lia)) as E33.
pose proof (EX 2%nat ltac:(lia)) as E34. pose proof (EX 3%nat ltac:(lia)) as E35.
pose proof (EX 4%nat ltac:(lia)) as E36.
cbn [Nat.add nth] in E32, E33, E34, E35, E36.
assert (U9 : bv_unsigned (ew E 9) = s)
  by (rewrite (EE 9%nat 9%bv eq_refl), R9; apply unsigned_lit_small; lia).
assert (U13 : bv_unsigned (ew E 13) = k)
  by (rewrite (EE 13%nat 13%bv eq_refl), R13; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = 3)
  by (rewrite (EE 22%nat 22%bv eq_refl), R22; apply unsigned_lit_small; lia).
assert (U26 : bv_unsigned (ew E 26) = SHADOW_OFF)
  by (rewrite (EE 26%nat 26%bv eq_refl), R26; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U32 : bv_unsigned (ew E 32) = a) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = b0) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = b1) by (rewrite E34; apply unsigned_lit_small; lia).
assert (U35 : bv_unsigned (ew E 35) = b3) by (rewrite E35; apply unsigned_lit_small; lia).
assert (U36 : bv_unsigned (ew E 36) = q) by (rewrite E36; apply unsigned_lit_small; lia).
split.
- rewrite restrict_mkst_fx. unfold sy_ss.
  apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
  + apply regs_ok_Eimg_Ereg.
  + vm_compute. reflexivity.
  + apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * unfold sy_rg_c, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U32. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
      -- apply (chunk_ok_val segs E _ a (-3) 1 (SOff 33 0) b0).
         ++ rewrite denot_lit_U, (U_atom E 33 b0 E33 ltac:(lia)). reflexivity.
         ++ cbn. lia.
         ++ cbn. lia.
         ++ replace (a + -3) with (a - 3) by lia. exact V0.
      -- apply (chunk_ok_val segs E _ a (-2) 1 (SOff 34 0) b1).
         ++ rewrite denot_lit_U, (U_atom E 34 b1 E34 ltac:(lia)). reflexivity.
         ++ cbn. lia.
         ++ cbn. lia.
         ++ replace (a + -2) with (a - 2) by lia. exact V1.
      -- apply (chunk_ok_val segs E _ a 0 1 (SOff 35 0) b3).
         ++ rewrite denot_lit_U, (U_atom E 35 b3 E35 ltac:(lia)). reflexivity.
         ++ cbn. lia.
         ++ cbn. lia.
         ++ rewrite Z.add_0_r. exact V3.
    * unfold sy_rg_s, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
      -- apply (chunk_ok_val segs E _ s 160 8 (SOff 36 0) q).
         ++ rewrite denot_lit_U, (U_atom E 36 q E36 ltac:(lia)). reflexivity.
         ++ cbn. lia.
         ++ cbn. lia.
         ++ exact VQ.
      -- apply (chunk_ok_val segs E _ s 176 8 (SOff 20 1) (c + 1)).
         ++ rewrite denot_lit_U, (U_atom_off E 20 c 1)
              by (first [rewrite (EE 20%nat 20%bv eq_refl); exact R20 | lia]).
            reflexivity.
         ++ cbn. lia.
         ++ cbn. lia.
         ++ exact VC.
  + cbn [pairwise_disjoint all_disjoint]. unfold extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val sy_rg_c sy_rg_s]. rewrite U32, U9.
    split; [split; [left; lia | exact I] | exact (conj I I)].
  + assert (HAL : sv_denot E (SAlu ALU_ADD (SOff 20 0) (SOff 13 0)) = sv_denot E (SOff 32 0)).
    { rewrite (denot_lit_U E (SAlu ALU_ADD (SOff 20 0) (SOff 13 0))), (denot_lit_U E (SOff 32 0)). f_equal.
      assert (UA20 : U E (SOff 20 0) = c) by (apply U_atom; [rewrite (EE 20%nat 20%bv eq_refl); exact R20 | lia]).
      assert (UA13 : U E (SOff 13 0) = k) by (apply U_atom; [rewrite (EE 13%nat 13%bv eq_refl); exact R13 | lia]).
      assert (UA32 : U E (SOff 32 0) = a) by (apply U_atom; [exact E32 | lia]).
      rewrite U_SAlu, UA20, UA13, UA32. cbn [zalu_raw]. rewrite zcanon_id by (unfold M64; lia). lia. }
    unfold sy_facts, facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    refine (conj _ (conj I (conj HAL I))).
    unfold afact_ok, YC4b.PTR. cbn [af_lo af_hi af_al2].
    rewrite U26, U32, U13, U22, U36, U33, U34, U35, !Z.pow_0_r, !Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end; try exact I; unfold SHADOW_OFF; lia.
- unfold sh_ok, SY_SH. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range segs (w_H W) mem E SY_Bx 32%nat (a - 3) 4 a (-3) 1 Hra).
  + unfold SY_Bx. apply U_atom; [rewrite (EE 26%nat 26%bv eq_refl); exact R26 | unfold SHADOW_OFF; lia].
  + apply U_atom; [exact E32 | lia].
  + lia.
  + lia.
  + intros x Hx. change (Z.min (-3) 1) with (-3) in Hx. change (Z.max (-3) 1) with 1 in Hx. apply Happ. lia.
Qed.

(* A seat with no region holds of any machine state at its pc. *)
Lemma sy_entry0 : forall (W : world segs) regs mem (pc : Z),
  st_ok_pi segs VAL (sy_E0 regs) (sy_ss0 pc)
    (restrict (w_H W) (@YK11.mkst fx regs (Z_to_bv 64 (BASE + pc)) mem (YK11.seg_rom segs))).
Proof.
intros W regs mem pc. rewrite restrict_mkst_fx. unfold sy_ss0.
apply (@pa_entry_st_ok_full fx rc transportb_listing PI_transportb).
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_nil.
- apply pairwise_disjoint_of_extents. cbn [map zpairwise_disjoint zall_disjoint]. exact I.
- unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok]. repeat split; exact I.
Qed.

End fx.

(* lc_core at other registers that agree on sp, gp, tp, s0 and s1. *)
Lemma sy_core_regs : forall cx ly' S' (W' : world segs) regs' regs2 mem' md' e,
  lc_core B cx ly' S' W' regs' mem' md' e ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv] -> YK11.getr regs2 r = YK11.getr regs' r) ->
  lc_core B cx ly' S' W' regs2 mem' md' e.
Proof.
intros cx ly' S' W' regs' regs2 mem' md' e H K.
destruct H as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hrest).
refine (conj HJ (conj Hfrs (conj HlyF (conj HPERM _)))).
rewrite !K by sy_in.
exact (conj Rsp (conj R8 (conj R9 (conj Rgp (conj Rtp Hrest))))).
Qed.

(* lc_tag_common across a stretch that keeps the memory at every address the view reads, the registers it names and
   (given) the core. *)
Lemma sy_tag_kept : forall cx op B1 ly' S' (W' : world segs) regs' mem' md' e regs2 mem2 md2,
  lc_tag_common B MT cx op B1 ly' S' W' regs' mem' md' e ->
  lc_core B cx ly' S' W' regs2 mem2 md2 e ->
  (forall x, mrestrict (w_H W') mem2 x = mrestrict (w_H W') mem' x) ->
  (forall r : bv 5, In r [18%bv; 19%bv; 20%bv; 23%bv; 24%bv; 26%bv; 27%bv] ->
     YK11.getr regs2 r = YK11.getr regs' r) ->
  lc_tag_common B MT cx op B1 ly' S' W' regs2 mem2 md2 e.
Proof.
intros cx op B1 ly' S' W' regs' mem' md' e regs2 mem2 md2 H Hcore2 HM K.
assert (Hm : mrestrict (w_H W') mem2 = mrestrict (w_H W') mem') by (apply functional_extensionality; exact HM).
assert (Ha : aview segs (w_H W') mem2 = aview segs (w_H W') mem') by (unfold aview; rewrite Hm; reflexivity).
unfold lc_tag_common, lc_lcore, lc_fr, lc_tw in *. cbv zeta in *.
rewrite Ha, Hm.
destruct H as (Hopc & (Hcore & (R18 & R26) & Hsp & Hfsh & Hopok & Hev & Hmet & R19) & Hob & Hraw & Hser & Htw &
  Hgc & H24 & H16 & H8 & H64 & R24 & R27 & R20 & R23).
rewrite !K by sy_in.
refine (conj Hopc (conj (conj Hcore2 (conj (conj R18 R26) (conj Hsp (conj Hfsh (conj Hopok (conj Hev
  (conj Hmet R19))))))) _)).
exact (conj Hob (conj Hraw (conj Hser (conj Htw (conj Hgc (conj H24 (conj H16 (conj H8 (conj H64 (conj R24
  (conj R27 (conj R20 R23)))))))))))).
Qed.

(* +0x112c after a miss at i: the state of SYSL(i) at the increment, with no hit at i either. *)
Definition sy_sysn (cx : lcx) (op : lop) (i : Z) : world segs -> config -> Prop :=
  fun W' c' => exists ly' S' regs' mem' md' e B1,
    let D := l_pl cx in
    let tv := lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D (lo_c op)))) in
    c' = lc_cfg cx LO_SYSN regs' mem' md' /\
    lc_tag_common B MT cx op B1 ly' S' W' regs' mem' md' e /\
    0 <= i < tg_len tv - 3 /\ i < 21 /\
    (forall j : nat, (j <= Z.to_nat i)%nat ->
       DSpec.sys_hit (firstn (Z.to_nat (tg_len tv)) (tg_cbytes tv)) j = false) /\
    YK11.getr regs' 12 = w64 (tg_len tv) /\ YK11.getr regs' 13 = w64 (i + 3) /\
    YK11.getr regs' 21 = w64 (TB_g_cmd + 40 * tg_serial tv) /\
    YK11.getr regs' 22 = w64 3 /\ YK11.getr regs' 25 = w64 0xf0.

Lemma sy_aview_eq : forall (H : word -> bool) (m m2 : word -> option byte),
  (forall x, mrestrict H m2 x = mrestrict H m x) -> forall a, aview segs H m2 a = aview segs H m a.
Proof. intros H m m2 Hpt a. unfold aview, mbyte. rewrite Hpt. reflexivity. Qed.

(* The state SYSN at a machine state a read-only stretch reached from SYSL(i), with the miss at i. *)
Lemma sy_mk_sysn : forall cx op i (W : world segs) ly' S' regs mem md e B1 regs2 mem2 md2,
  let D := l_pl cx in
  let tv := lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D (lo_c op)))) in
  lc_tag_common B MT cx op B1 ly' S' W regs mem md e ->
  0 <= i < tg_len tv - 3 -> i < 21 ->
  (forall j : nat, (j < Z.to_nat i)%nat -> DSpec.sys_hit (firstn (Z.to_nat (tg_len tv)) (tg_cbytes tv)) j = false) ->
  YK11.getr regs 12 = w64 (tg_len tv) -> YK11.getr regs 13 = w64 (i + 3) ->
  YK11.getr regs 21 = w64 (TB_g_cmd + 40 * tg_serial tv) -> YK11.getr regs 22 = w64 3 ->
  YK11.getr regs 25 = w64 0xf0 ->
  lc_core B cx ly' S' W regs mem2 md2 e ->
  (forall x, mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem x) ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 13%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv;
     24%bv; 25%bv; 26%bv; 27%bv] -> YK11.getr regs2 r = YK11.getr regs r) ->
  DSpec.sys_hit (firstn (Z.to_nat (tg_len tv)) (tg_cbytes tv)) (Z.to_nat i) = false ->
  sy_sysn cx op i W (lc_cfg cx LO_SYSN regs2 mem2 md2).
Proof.
intros cx op i W ly' S' regs mem md e B1 regs2 mem2 md2 D tv Htc Hi Hi21 Hnh R12 R13 R21 R22 R25
  Hcore2 KM KR Hmiss.
exists ly', S', regs2, mem2, md2, e, B1. cbv zeta. fold D tv.
split; [reflexivity|].
split.
{ apply (sy_tag_kept cx op B1 ly' S' W regs mem md e regs2 mem2 md2 Htc); [| exact KM |].
  - apply (sy_core_regs cx ly' S' W regs regs2 mem2 md2 e Hcore2). intros r Hr. apply KR.
    cbn [In] in Hr |- *. tauto.
  - intros r Hr. apply KR. cbn [In] in Hr |- *. tauto. }
split; [exact Hi|]. split; [exact Hi21|].
split.
{ intros j Hj. destruct (Nat.eq_dec j (Z.to_nat i)) as [-> | Hne]; [exact Hmiss | apply Hnh; lia]. }
rewrite !KR by sy_in.
exact (conj R12 (conj R13 (conj R21 (conj R22 R25)))).
Qed.

(* An atom plus a constant, as the increment leaves it. *)
Lemma sy_denot_off : forall (E : env) n x c, ew E n = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 ->
  0 <= x + c < 2 ^ 64 -> sv_denot E (SOff n c) = Z_to_bv 64 (x + c).
Proof.
intros E n x c Hn Hx Hc. rewrite denot_lit_U. f_equal. apply (U_atom_off E n x c Hn Hx Hc).
Qed.

(* The state SYSJ at a machine state a read-only stretch reached, t2 the sys flag. *)
Lemma sy_mk_sysj : forall cx op (W : world segs) ly' S' regs mem md e B1 regs2 mem2 md2 (s : bool),
  let tv := lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)))) in
  lc_tag_common B MT cx op B1 ly' S' W regs mem md e ->
  YK11.getr regs 21 = w64 (TB_g_cmd + 40 * tg_serial tv) ->
  lc_core B cx ly' S' W regs mem2 md2 e ->
  (forall x, mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem x) ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 26%bv; 27%bv] ->
     YK11.getr regs2 r = YK11.getr regs r) ->
  lc_sys tv = s ->
  YK11.getr regs2 7 = w64 (if s then 1 else 0) ->
  lc_st_sysj B MT cx op W (lc_cfg cx LO_SYSJ regs2 mem2 md2).
Proof.
intros cx op W ly' S' regs mem md e B1 regs2 mem2 md2 s tv Htc R21 Hcore2 KM KR Hs Q7.
exists ly', S', regs2, mem2, md2, e, B1. cbv zeta. fold tv.
split; [reflexivity|].
split.
{ apply (sy_tag_kept cx op B1 ly' S' W regs mem md e regs2 mem2 md2 Htc); [| exact KM |].
  - apply (sy_core_regs cx ly' S' W regs regs2 mem2 md2 e Hcore2). intros r Hr. apply KR.
    cbn [In] in Hr |- *. tauto.
  - intros r Hr. apply KR. cbn [In] in Hr |- *. tauto. }
split; [rewrite Hs; exact Q7|].
rewrite KR by sy_in. exact R21.
Qed.

(* The state SYSL(i + 1) at a machine state the increment reached from SYSN(i). *)
Lemma sy_mk_sysl : forall cx op i (W : world segs) ly' S' regs mem md e B1 regs2 mem2 md2,
  let D := l_pl cx in
  let tv := lc_tag_vals D B1 (sv_c (lc_sub_kd D (lc_oc D (lo_c op)))) in
  lc_tag_common B MT cx op B1 ly' S' W regs mem md e ->
  0 <= i < tg_len tv - 3 -> i + 1 <> tg_len tv - 3 -> tg_len tv <= 24 ->
  (forall j : nat, (j <= Z.to_nat i)%nat -> DSpec.sys_hit (firstn (Z.to_nat (tg_len tv)) (tg_cbytes tv)) j = false) ->
  YK11.getr regs 12 = w64 (tg_len tv) -> YK11.getr regs 21 = w64 (TB_g_cmd + 40 * tg_serial tv) ->
  YK11.getr regs 22 = w64 3 -> YK11.getr regs 25 = w64 0xf0 ->
  lc_core B cx ly' S' W regs mem2 md2 e ->
  (forall x, mrestrict (w_H W) mem2 x = mrestrict (w_H W) mem x) ->
  (forall r : bv 5, In r [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv;
     25%bv; 26%bv; 27%bv] -> YK11.getr regs2 r = YK11.getr regs r) ->
  YK11.getr regs2 13 = w64 (i + 1 + 3) ->
  lc_st_sysl B MT cx op (i + 1) W (lc_cfg cx LO_SYSL regs2 mem2 md2).
Proof.
intros cx op i W ly' S' regs mem md e B1 regs2 mem2 md2 D tv Htc Hi Hne Hl24 Hnh R12 R21 R22 R25
  Hcore2 KM KR Q13.
exists ly', S', regs2, mem2, md2, e, B1. cbv zeta. fold D tv.
split; [reflexivity|].
split.
{ apply (sy_tag_kept cx op B1 ly' S' W regs mem md e regs2 mem2 md2 Htc); [| exact KM |].
  - apply (sy_core_regs cx ly' S' W regs regs2 mem2 md2 e Hcore2). intros r Hr. apply KR.
    cbn [In] in Hr |- *. tauto.
  - intros r Hr. apply KR. cbn [In] in Hr |- *. tauto. }
split; [lia|]. split; [lia|].
split; [intros j Hj; apply Hnh; lia|].
split; [rewrite KR by sy_in; exact R12|]. split; [exact Q13|].
rewrite !KR by sy_in. exact (conj R21 (conj R22 R25)).
Qed.

(* +0x112c .. +0x1130 and the exit: the next turn's head, or SYSJ with no hit. *)
Lemma sy_tail : lp_prem B MT XL RLO RHI -> forall cx op i (W : world segs) c, lc_base B MT XL RLO RHI cx ->
  sy_sysn cx op i W c ->
  SRr segs W c (fun W2 c2 => lc_st_sysl B MT cx op (i + 1) W2 c2 \/ lc_st_sysj B MT cx op W2 c2).
Proof.
intros HP cx op i W c HB HN.
destruct HN as (ly' & S' & regs & mem & md & e & B1 & HN). cbv zeta in HN.
destruct HN as (-> & Htc & Hi & Hi21 & Hnh & R12 & R13 & R21 & R22 & R25).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof Htc as (Hopc & (Hcore & _ & _ & _ & Hopok & _) & _).
pose proof Hcore as (HJ & _).
set (D := l_pl cx) in *.
set (c3 := sv_c (lc_sub_kd D (lc_oc D (lo_c op)))) in *.
set (tv := lc_tag_vals D B1 c3) in *.
assert (Hc3 : QF.fuzz_in_ok D c3) by (apply sy_kd_ok; exact (proj1 (proj2 (proj2 Hopok)))).
destruct (sy_cb_len D B1 c3 Hc3) as (Hcbl & Hlen).
fold tv in Hcbl, Hlen.
set (cb := firstn (Z.to_nat (tg_len tv)) (tg_cbytes tv)) in *.
pose proof (sy_entry0 (fx := l_fx cx) W regs mem LO_SYSN) as HS.
set (E0 := sy_E0 regs) in *.
assert (SHOK : sh_ok segs SY_Bx (@nil shent) E0 (mrestrict (w_H W) mem)) by constructor.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0, sy_E0; apply Eimg_env).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros nq rq Hnq; unfold E0, sy_E0; apply can_ew_Eimg_Ereg_nat; exact Hnq).
assert (HAE : forall Ex, (forall n, (n < 240)%nat -> ew Ex n = ew E0 n) -> ed Ex = ed E0 ->
  env_agree 32 (Ereg regs []) Ex).
{ intros Ex AG HD. split; [intros nn Hnn; rewrite (AG nn) by lia; unfold E0, sy_E0; apply Eimg_low; unfold A_TEXT; lia
                         | rewrite HD; reflexivity]. }
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + LO_SYSN)) mem
    (YK11.seg_rom segs)) md) Q) end.
(* +0x112c .. +0x1130: a3 + 1, `bne a2, a3` *)
paj_run_tok RUN HS HJ SHOK SY_B0.
{ sy_awr. }
sy_md. sy_km HFr KM1. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (AG1 : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
    by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
assert (X12 : ew E0 12 = Z_to_bv 64 (tg_len tv)) by (rewrite (EE 12%nat 12%bv eq_refl); exact R12).
assert (X13 : ew E0 13 = Z_to_bv 64 (i + 3)) by (rewrite (EE 13%nat 13%bv eq_refl); exact R13).
psrr_branch_tok RUN BR HS SHOK SY_B0.
- (* len <> i + 4, i.e. i + 1 <> len - 3: back to +0x10b0, the head of turn i + 1 *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom _ 12 (tg_len tv)) in Hc by (first [exact X12 | rewrite AG1 by lia; exact X12 | lia]).
  rewrite (U_atom_off _ 13 (i + 3) 1) in Hc by (first [exact X13 | rewrite AG1 by lia; exact X13 | lia]).
  apply negb_true_iff, Z.eqb_neq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK SY_B0 LO_SYSL.
  { sy_awr. }
  sy_md. sy_km HFr KM2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG2 : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG1; exact Hnn]) end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs []
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv; 26%bv; 27%bv]
      HS (HAE Ex AG2 eq_refl) ltac:(vm_compute; reflexivity)) as KR;
    assert (KM : forall x, mrestrict (w_H W) (ms_mem msx) x = mrestrict (w_H W) mem x)
      by (intros x; rewrite KM2, KM1; reflexivity)
  end.
  sy_reg_at HS (13%bv : bv 5) (w64 (i + 1 + 3)) Q13
    ltac:(rewrite (sy_denot_off _ 13 (i + 3) 1);
          [apply (f_equal (Z_to_bv 64)); lia | first [exact X13 | rewrite AG2 by lia; exact X13] | lia | lia]).
  pose proof (sy_aview_eq (w_H W) mem _ KM) as KV.
  pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W regs mem md e 0 ly' S' W regs _ _ e HB Hcore HJ
    eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia)
    (fun a _ _ => KV a) (fun j _ => KV (l_p cx + j)) (fun a _ => KV a)
    (fun a _ Hp => sy_present (w_H W) mem _ KM a Hp)) as Hcore2.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (lc_cfg cx LO_SYSL rg mm mdx) Q) end.
  assert (Hne : i + 1 <> tg_len tv - 3) by lia.
  apply SRr_ret. left.
  exact (sy_mk_sysl cx op i W ly' S' regs mem md e B1 _ _ _ Htc Hi Hne (proj2 Hlen) Hnh R12 R21 R22 R25
    Hcore2 KM KR Q13).
- (* len = i + 4: the last turn, +0x1134 `j`, +0x1164 .. +0x116c, SYSJ with t2 = 0 *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom _ 12 (tg_len tv)) in Hc by (first [exact X12 | rewrite AG1 by lia; exact X12 | lia]).
  rewrite (U_atom_off _ 13 (i + 3) 1) in Hc by (first [exact X13 | rewrite AG1 by lia; exact X13 | lia]).
  apply negb_false_iff, Z.eqb_eq in Hc.
  paj_run_to_tok RUNTO HS HJ SHOK SY_B0 LO_SYSJ.
  { sy_awr. }
  sy_md. sy_km HFr KM2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG2 : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG1; exact Hnn]) end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs []
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 26%bv; 27%bv]
      HS (HAE Ex AG2 eq_refl) ltac:(vm_compute; reflexivity)) as KR;
    assert (KM : forall x, mrestrict (w_H W) (ms_mem msx) x = mrestrict (w_H W) mem x)
      by (intros x; rewrite KM2, KM1; reflexivity)
  end.
  sy_reg_at HS (7%bv : bv 5) (w64 0) Q7 ltac:(reflexivity).
  pose proof (sy_aview_eq (w_H W) mem _ KM) as KV.
  pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W regs mem md e 0 ly' S' W regs _ _ e HB Hcore HJ
    eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia)
    (fun a _ _ => KV a) (fun j _ => KV (l_p cx + j)) (fun a _ => KV a)
    (fun a _ Hp => sy_present (w_H W) mem _ KM a Hp)) as Hcore2.
  assert (Hsys : lc_sys tv = false).
  { change (lc_sys tv) with (DSpec.system_at cb). apply DSpec.system_at_false.
    intros j Hj. unfold cb in Hj. rewrite firstn_length_le in Hj by lia. apply Hnh. lia. }
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (lc_cfg cx LO_SYSJ rg mm mdx) Q) end.
  apply SRr_ret. right.
  exact (sy_mk_sysj cx op W ly' S' regs mem md e B1 _ _ _ false Htc R21 Hcore2 KM KR Hsys Q7).
Qed.

Lemma lc_op4sys_ok : lc_op4sys_stmt B MT XL RLO RHI.
Proof.
unfold lc_op4sys_stmt.
intros HP cx op i W c HB HL.
destruct HL as (ly' & S' & regs & mem & md & e & B1 & HL). cbv zeta in HL.
destruct HL as (-> & Htc & Hi & Hi21 & Hnh & R12 & R13 & R21 & R22 & R25).
pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
pose proof Htc as (Hopc & (Hcore & (R18 & R26) & Hsp & Hfsh & Hopok & Hev & Hmet & R19) & Hob & Hraw & Hser & Htw &
  Hgc & H24 & H16 & H8 & H64 & R24 & R27 & R20 & R23).
pose proof (lc_geom B MT XL RLO RHI cx ly' S' W regs mem md e HB Hcore) as G.
destruct G as [HAR Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
pose proof Hcore as (HJ & Hfrs & HlyF & HPERM & Rsp & R8 & R9 & Rgp & Rtp & Hsp1 & Hsp1al & HSAV & HF4096 & HFal &
  HFceil & HFpres & HFL & HIN).
destruct (frames_bounds tfibsegs B LAWS ly' S' W mem md LF_CID (l_fpos cx) HAR HFin) as (_ & _ & Happ).
rewrite HFaddr in Happ. change (fs_frame_bytes LF_CID) with LF_FBYTES in Happ.
pose proof asan_consts as ((CVlo & CVhi) & _).
set (D := l_pl cx) in *.
set (c3 := sv_c (lc_sub_kd D (lc_oc D (lo_c op)))) in *.
set (tv := lc_tag_vals D B1 c3) in *.
assert (Hc3 : QF.fuzz_in_ok D c3) by (apply sy_kd_ok; exact (proj1 (proj2 (proj2 Hopok)))).
destruct (sy_cb_len D B1 c3 Hc3) as (Hcbl & Hlen).
fold tv in Hcbl, Hlen.
set (cb := firstn (Z.to_nat (tg_len tv)) (tg_cbytes tv)) in *.
set (kd := lc_sub_kd D (lc_oc D (lo_c op))) in *.
assert (HgL : length (TW.zs (TOP.cmd_struct (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd))) = 32%nat)
  by (apply sy_c_len; exact Hcbl).
assert (VB : forall j : nat, (j < Z.to_nat (tg_len tv))%nat ->
  val_mem segs (mrestrict (w_H W) mem) (lc_F cx + 32 + Z.of_nat j) 1 (DSpec.at8 cb j) /\
  0 <= DSpec.at8 cb j < 256).
{ intros j Hj. destruct (Hgc j ltac:(rewrite HgL; lia)) as (Hv & Hr).
  rewrite (sy_c_byte (tg_cbytes tv) (tg_len tv) _ _ j Hcbl ltac:(lia) Hj) in Hv, Hr. exact (conj Hv Hr). }
destruct (VB (Z.to_nat i) ltac:(lia)) as (V0 & B0r).
destruct (VB (S (Z.to_nat i)) ltac:(lia)) as (V1 & B1r).
destruct (VB (S (S (S (Z.to_nat i)))) ltac:(lia)) as (V3 & B3r).
set (b0 := DSpec.at8 cb (Z.to_nat i)) in *.
set (b1 := DSpec.at8 cb (S (Z.to_nat i))) in *.
set (b3 := DSpec.at8 cb (S (S (S (Z.to_nat i))))) in *.
pose (a := lc_F cx + 32 + i + 3). assert (Ea : a = lc_F cx + 32 + i + 3) by reflexivity. clearbody a.
replace (lc_F cx + 32 + Z.of_nat (Z.to_nat i)) with (a - 3) in V0 by lia.
replace (lc_F cx + 32 + Z.of_nat (S (Z.to_nat i))) with (a - 2) in V1 by lia.
replace (lc_F cx + 32 + Z.of_nat (S (S (S (Z.to_nat i))))) with a in V3 by lia.
(* the spill slots 160(s1) and 176(s1) *)
unfold lc_spills in Hsp. rewrite Forall_forall in Hsp.
pose proof (Hsp (160, 2 ^ 64 - 1 - (lc_F cx + 32))
  ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [app]; sy_in)) as S160.
pose proof (Hsp (176, lc_F cx + 33)
  ltac:(unfold lf_spill_loop, lf_spill_init, lf_spill_scal, lf_spill_sm; cbn [app]; sy_in)) as S176.
cbn [fst snd] in S160, S176.
pose proof (val_mem_of_rdword segs (w_H W) mem _ _ S160) as VQ.
pose proof (val_mem_of_rdword segs (w_H W) mem _ _ S176) as VC.
replace (lc_F cx + 33) with (lc_F cx + 32 + 1) in VC by lia.
unfold in_app, kLowShadowBeg, kHighMemBeg, LF_FBYTES in Happ.
unfold LF_FBYTES in HFceil. unfold LF_FRAME in Hsp1.
assert (HRA : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (a - 3) 4).
{ apply (sy_ra cx _ Hfsh HFal); lia. }
assert (HAPP : forall x, a - 3 <= x < a + 1 -> ~ (SHADOW_OFF <= x < SHADOW_OFF + 17592186044416)).
{ intros x Hx. unfold SHADOW_OFF. destruct Happ as (Ha1 & [Ha2 | (Ha2 & Ha3)]); lia. }
destruct Hstk as (Hstk1 & Hstk2 & Hstk3 & Hstk4).
destruct (sy_entry (fx := l_fx cx) W regs mem (lc_F cx + 32) (i + 3) (lc_sp1 cx) a b0 b1 b3
  (2 ^ 64 - 1 - (lc_F cx + 32)) R20 R13 R9 R26 R22 ltac:(lia) eq_refl ltac:(lia) ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) V0 V1 V3 VQ VC B0r B1r B3r HRA HAPP) as (HS & SHOK).
assert (HEI : img_env VAL A_LIM (sy_E regs a b0 b1 b3 (2 ^ 64 - 1 - (lc_F cx + 32))))
  by (unfold sy_E; apply Eimg_env).
pose proof (@paj_run_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUN.
pose proof (@paj_run_to_x (l_fx cx) rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS
  TG.G_HARNESS_B HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := l_fx cx) (PI := PI_transportb)) as BR.
set (E0 := sy_E regs a b0 b1 b3 (2 ^ 64 - 1 - (lc_F cx + 32))) in *.
unfold lc_cfg.
lazymatch goal with |- SRr _ ?Wx _ ?Q =>
  change (SRr segs Wx (mkCfg (@YK11.mkst (l_fx cx) regs (Z_to_bv 64 (BASE + LO_SYSL)) mem
    (YK11.seg_rom segs)) md) Q) end.
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = YK11.getr regs r)
  by (intros nq rq Hnq; unfold E0, sy_E; apply can_ew_Eimg_Ereg_nat; exact Hnq).
assert (EX : forall j, (j < 5)%nat -> ew E0 (32 + j) =
  nth j [w64 a; w64 b0; w64 b1; w64 b3; w64 (2 ^ 64 - 1 - (lc_F cx + 32))] (Z_to_bv 64 0))
  by (intros jq Hjq; unfold E0, sy_E; rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_extra).
pose proof (EX 1%nat ltac:(lia)) as E33. pose proof (EX 2%nat ltac:(lia)) as E34.
pose proof (EX 3%nat ltac:(lia)) as E35. cbn [Nat.add nth] in E33, E34, E35. clear EX.
pose proof (EE 25%nat 25%bv eq_refl) as E25. rewrite R25 in E25.
assert (HAE : forall Ex, (forall n, (n < 240)%nat -> ew Ex n = ew E0 n) -> ed Ex = ed E0 ->
  env_agree 32 (Ereg regs [w64 a; w64 b0; w64 b1; w64 b3; w64 (2 ^ 64 - 1 - (lc_F cx + 32))]) Ex).
{ intros Ex AG HD. split; [intros nn Hnn; rewrite (AG nn) by lia; unfold E0, sy_E; apply Eimg_low; unfold A_TEXT; lia
                         | rewrite HD; reflexivity]. }
(* +0x10b0 .. +0x10d8: a0 = c + i + 3 (the trap test +0x10b4 decided), the check of c[i], a1 = c[i], `bne a1, s9` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ sy_awr. }
sy_md. sy_km HFr KM1. clear HF HFr HG.
lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
  assert (AG1 : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
    by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; reflexivity) end.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* c[i] <> 0xf0: to +0x112c *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom _ 33 b0) in Hc by (first [rewrite AG1 by lia; exact E33 | lia]).
  rewrite (U_atom _ 25 240) in Hc by (first [rewrite AG1 by lia; exact E25 | lia]).
  apply negb_true_iff, Z.eqb_neq in Hc.
  assert (Hmiss : DSpec.sys_hit cb (Z.to_nat i) = false).
  { unfold DSpec.sys_hit. change (DSpec.at8 cb (Z.to_nat i)) with b0.
    rewrite (proj2 (Z.eqb_neq b0 0xf0) Hc). reflexivity. }
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SYSN.
  { sy_awr. }
  sy_md. sy_km HFr KM2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG2 : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG1; exact Hnn]) end.
  lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
    pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs
      [w64 a; w64 b0; w64 b1; w64 b3; w64 (2 ^ 64 - 1 - (lc_F cx + 32))]
      [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 13%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
       26%bv; 27%bv] HS (HAE Ex AG2 eq_refl) ltac:(vm_compute; reflexivity)) as KR;
    assert (KM : forall x, mrestrict (w_H W) (ms_mem msx) x = mrestrict (w_H W) mem x)
      by (intros x; rewrite KM2, KM1; reflexivity)
  end.
  pose proof (sy_aview_eq (w_H W) mem _ KM) as KV.
  pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W regs mem md e 0 ly' S' W regs _ _ e HB Hcore HJ
    eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia)
    (fun a _ _ => KV a) (fun j _ => KV (l_p cx + j)) (fun a _ => KV a)
    (fun a _ Hp => sy_present (w_H W) mem _ KM a Hp)) as Hcore2.
  pmkst HS.
  lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
    change (SRr sg Wx (lc_cfg cx LO_SYSN rg mm mdx) Q) end.
  apply (sy_tail HP cx op i W _ HB).
  exact (sy_mk_sysn cx op i W ly' S' regs mem md e B1 _ _ _ Htc Hi Hi21 Hnh R12 R13 R21 R22 R25
    Hcore2 KM KR Hmiss).
- (* c[i] = 0xf0: the trap test +0x10e4 decided, the check of c[i + 1], a1 = c[i + 1], `bne a1, a6` (a6 = 0x13) *)
  rewrite branch_ne_U in Hc.
  rewrite (U_atom _ 33 b0) in Hc by (first [rewrite AG1 by lia; exact E33 | lia]).
  rewrite (U_atom _ 25 240) in Hc by (first [rewrite AG1 by lia; exact E25 | lia]).
  apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb0.
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { sy_awr. }
  sy_md. sy_km HFr KM2. clear HF HFr HG.
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (AG2 : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
      by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG1; exact Hnn]) end.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* c[i + 1] <> 0x13: to +0x112c *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom _ 34 b1) in Hc by (first [rewrite AG2 by lia; exact E34 | lia]).
    rewrite U_lit in Hc by lia.
    apply negb_true_iff, Z.eqb_neq in Hc.
    assert (Hmiss : DSpec.sys_hit cb (Z.to_nat i) = false).
    { unfold DSpec.sys_hit. change (DSpec.at8 cb (Z.to_nat i)) with b0. change (DSpec.at8 cb (S (Z.to_nat i))) with b1.
      rewrite (proj2 (Z.eqb_eq b0 0xf0) Hb0), (proj2 (Z.eqb_neq b1 0x13) Hc). reflexivity. }
    paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SYSN.
    { sy_awr. }
    sy_md. sy_km HFr KM3. clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (AG3 : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
        by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG2; exact Hnn]) end.
    lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
      pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs
        [w64 a; w64 b0; w64 b1; w64 b3; w64 (2 ^ 64 - 1 - (lc_F cx + 32))]
        [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 13%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
         26%bv; 27%bv] HS (HAE Ex AG3 eq_refl) ltac:(vm_compute; reflexivity)) as KR;
      assert (KM : forall x, mrestrict (w_H W) (ms_mem msx) x = mrestrict (w_H W) mem x)
        by (intros x; rewrite KM3, KM2, KM1; reflexivity)
    end.
    pose proof (sy_aview_eq (w_H W) mem _ KM) as KV.
    pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W regs mem md e 0 ly' S' W regs _ _ e HB Hcore HJ
      eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia)
      (fun a _ _ => KV a) (fun j _ => KV (l_p cx + j)) (fun a _ => KV a)
      (fun a _ Hp => sy_present (w_H W) mem _ KM a Hp)) as Hcore2.
    pmkst HS.
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (lc_cfg cx LO_SYSN rg mm mdx) Q) end.
    apply (sy_tail HP cx op i W _ HB).
    exact (sy_mk_sysn cx op i W ly' S' regs mem md e B1 _ _ _ Htc Hi Hi21 Hnh R12 R13 R21 R22 R25
      Hcore2 KM KR Hmiss).
  + (* c[i + 1] = 0x13: the trap test +0x110c decided, the check of c[i + 3], a0 = c[i + 3], `beq a0, a1`
       (a1 = 0x70) *)
    rewrite branch_ne_U in Hc.
    rewrite (U_atom _ 34 b1) in Hc by (first [rewrite AG2 by lia; exact E34 | lia]).
    rewrite U_lit in Hc by lia.
    apply negb_false_iff, Z.eqb_eq in Hc. rename Hc into Hb1.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { sy_awr. }
    sy_md. sy_km HFr KM3. clear HF HFr HG.
    lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
      assert (AG3 : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
        by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG2; exact Hnn]) end.
    psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
    * (* c[i + 3] = 0x70: a hit, +0x1168 / +0x116c to SYSJ with t2 = 1 *)
      rewrite branch_eq_U in Hc.
      rewrite (U_atom _ 35 b3) in Hc by (first [rewrite AG3 by lia; exact E35 | lia]).
      rewrite U_lit in Hc by lia.
      apply Z.eqb_eq in Hc. rename Hc into Hb3.
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SYSJ.
      { sy_awr. }
      sy_md. sy_km HFr KM4. clear HF HFr HG.
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
        assert (AG4 : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
          by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG3; exact Hnn]) end.
      lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
        pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs
          [w64 a; w64 b0; w64 b1; w64 b3; w64 (2 ^ 64 - 1 - (lc_F cx + 32))]
          [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 18%bv; 19%bv; 20%bv; 21%bv; 23%bv; 24%bv; 26%bv; 27%bv] HS
          (HAE Ex AG4 eq_refl) ltac:(vm_compute; reflexivity)) as KR;
        assert (KM : forall x, mrestrict (w_H W) (ms_mem msx) x = mrestrict (w_H W) mem x)
          by (intros x; rewrite KM4, KM3, KM2, KM1; reflexivity)
      end.
      sy_reg_at HS (7%bv : bv 5) (w64 1) Q7 ltac:(reflexivity).
      pose proof (sy_aview_eq (w_H W) mem _ KM) as KV.
      pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W regs mem md e 0 ly' S' W regs _ _ e HB Hcore HJ
        eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia)
        (fun a _ _ => KV a) (fun j _ => KV (l_p cx + j)) (fun a _ => KV a)
        (fun a _ Hp => sy_present (w_H W) mem _ KM a Hp)) as Hcore2.
      assert (Hsys : lc_sys tv = true).
      { change (lc_sys tv) with (DSpec.system_at cb). apply DSpec.system_at_true.
        exists (Z.to_nat i). split.
        - unfold cb. rewrite firstn_length_le by lia. lia.
        - unfold DSpec.sys_hit. change (DSpec.at8 cb (Z.to_nat i)) with b0.
          change (DSpec.at8 cb (S (Z.to_nat i))) with b1. change (DSpec.at8 cb (S (S (S (Z.to_nat i))))) with b3.
          rewrite (proj2 (Z.eqb_eq b0 0xf0) Hb0), (proj2 (Z.eqb_eq b1 0x13) Hb1), (proj2 (Z.eqb_eq b3 0x70) Hb3).
          reflexivity. }
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (lc_cfg cx LO_SYSJ rg mm mdx) Q) end.
      apply SRr_ret. right.
      exact (sy_mk_sysj cx op W ly' S' regs mem md e B1 _ _ _ true Htc R21 Hcore2 KM KR Hsys Q7).
    * (* c[i + 3] <> 0x70: to +0x112c *)
      rewrite branch_eq_U in Hc.
      rewrite (U_atom _ 35 b3) in Hc by (first [rewrite AG3 by lia; exact E35 | lia]).
      rewrite U_lit in Hc by lia.
      apply Z.eqb_neq in Hc.
      assert (Hmiss : DSpec.sys_hit cb (Z.to_nat i) = false).
      { unfold DSpec.sys_hit. change (DSpec.at8 cb (Z.to_nat i)) with b0.
        change (DSpec.at8 cb (S (Z.to_nat i))) with b1. change (DSpec.at8 cb (S (S (S (Z.to_nat i))))) with b3.
        rewrite (proj2 (Z.eqb_eq b0 0xf0) Hb0), (proj2 (Z.eqb_eq b1 0x13) Hb1), (proj2 (Z.eqb_neq b3 0x70) Hc).
        reflexivity. }
      paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan LO_SYSN.
      { sy_awr. }
      sy_md. sy_km HFr KM4. clear HF HFr HG.
      lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
        assert (AG4 : forall n, (n < 240)%nat -> ew Ex n = ew E0 n)
          by (intros nn Hnn; repeat rewrite ew_ewset_other by lia; first [reflexivity | apply AG3; exact Hnn]) end.
      lazymatch type of HS with st_ok_pi _ _ ?Ex ?ssx (restrict (w_H W) ?msx) =>
        pose proof (regs_kept_of_st_ok_pi Ex ssx (restrict (w_H W) msx) regs
          [w64 a; w64 b0; w64 b1; w64 b3; w64 (2 ^ 64 - 1 - (lc_F cx + 32))]
          [2%bv; 3%bv; 4%bv; 8%bv; 9%bv; 12%bv; 13%bv; 18%bv; 19%bv; 20%bv; 21%bv; 22%bv; 23%bv; 24%bv; 25%bv;
           26%bv; 27%bv] HS (HAE Ex AG4 eq_refl) ltac:(vm_compute; reflexivity)) as KR;
        assert (KM : forall x, mrestrict (w_H W) (ms_mem msx) x = mrestrict (w_H W) mem x)
          by (intros x; rewrite KM4, KM3, KM2, KM1; reflexivity)
      end.
      pose proof (sy_aview_eq (w_H W) mem _ KM) as KV.
      pose proof (lc_core_kept B MT XL RLO RHI cx ly' S' W regs mem md e 0 ly' S' W regs _ _ e HB Hcore HJ
        eq_refl (Permutation_refl _) (fun r _ => eq_refl) ltac:(unfold LLVMF_STK; lia)
        (fun a _ _ => KV a) (fun j _ => KV (l_p cx + j)) (fun a _ => KV a)
        (fun a _ Hp => sy_present (w_H W) mem _ KM a Hp)) as Hcore2.
      pmkst HS.
      lazymatch goal with |- SRr ?sg ?Wx (mkCfg (@YK11.mkst _ ?rg _ ?mm ?rom) ?mdx) ?Q =>
        change (SRr sg Wx (lc_cfg cx LO_SYSN rg mm mdx) Q) end.
      apply (sy_tail HP cx op i W _ HB).
      exact (sy_mk_sysn cx op i W ly' S' regs mem md e B1 _ _ _ Htc Hi Hi21 Hnh R12 R13 R21 R22 R25
        Hcore2 KM KR Hmiss).
Qed.

End sy.
