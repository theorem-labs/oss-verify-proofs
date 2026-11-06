(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the program walk of check_round_trip on the ASan build of plugin-hostd/fuzz_command
   (0x87fd8, 286 instructions), proving tcheck_round_trip_spec (check_round_trip_c.v), in the shape of cgif_file_fuzzer's
   walks (lib/A/AChc.v, ACh1..ACh8.v, AChf.v): one statement per point between two calls (ST_B .. ST_EPI below), each
   segment proved by a run of the symbolic executor over the position-abstract listing (CmdPaLib.v) from a fresh seed,
   the inline checks removed by the shadow tokens (PaShadow.v), and the call at its end composed into the journal:
   the class-5 side-stack frame by aj_stack_malloc_atS (PaCall.v) and, from check_round_trip_k.v, aj_set_shadow_atS
   (__asan_set_shadow_f8/_00) and aj_stack_free_cls_atS (__asan_stack_free_5); the strdup wrapper by crts4_strdup_sub,
   the free wrapper by afree04_sub (PaCall.v), the strcmp wrapper by aj_art_at (PaArt.v); the program callees
   rec_calls_copy, joined, send_message and rec_calls_free by cl_callS_wide and rec_calls_equal by cl_callS_na
   (PaNoChain.v), each with its contract as a Section hypothesis. The skip path (no word, or the daemon did not act)
   joins the epilogue at 0x88314; the abort edges (0x8838c) are excluded by rt_okA and the callees' posts.
   Re-fit to statement passes 4, 4b and 5: the callee and runtime hypotheses hold at every
   FP state (forall fx0) and the segments use them at the ambient fx. send_message reaches the printf wrappers, so the
   points before its return (ST_B .. ST_F) prove the FP-existential post crt_postF (apost_baseF); crt_s6 calls
   send_message by PaFx.v's cl_callS_wideF with the rounding-mode premise HFRM and goes on at the FP state fx1 it
   returns (srr_after_callF_base). The points after it (ST_G .. ST_EPI) prove apost_base at the ambient FP state, so
   once the sections close they hold at fx1 (crt_G, used so by tcheck_round_trip_spec_holds). The skip path lifts
   ST_EPI's post by apost_baseF_of_base (crts3_skip). Pass 5 removed astack_pres: s0 is the frame pointer sp0 at every
   call, so each call's frame chain is the prologue's frame record (ra at sp0 - 8, the entry s0 at sp0 - 16, from
   crt_frame) on afn_pre's chain (achain_push, crt_chain), and chain_pre for the runtime allocation entries is
   achain_chain_pre of it. joined's new premises at its call: len's 8 bytes present (the journal's window), and
   (pass 5b) the stack from len - 16 present, from the statement's astack_pres kept by astack_pres_journal. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 623 of its 702 lines of code are new or changed and 4974 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca): the NEW sub-walk of
   segment B8b of reac_segconf_parse_file's walk, pb8b_new_holds : forall n, HA_B8B_JOIN B n -> H_NEW B n
   (NEW 0x88e54 -> JOIN 0x88f00, lib/B/Prog/pf_pieces.v's INV_NEW and lib/B/Prog/pf_seg_B8b_d.v's INV_B8B_JOIN).
   A B8b sub-lane of the image-B G3 walk owner, 2026-10-30.
   proves function reac_segconf_parse_file (segment B8b, the NEW piece; reuse search and CONFIRM:
   the rule-24 lookup record, the rule-24 checker 2026-10-30T16:55:47Z; verdict none).
   ADAPTED from a working branch (lib/A/Prog/pf_a8b_m.v / _k.v / _t.v, here the ports pf_seg_B8b_m.v /
   _k.v / _t.v) and from the image-B walks lib/B/Prog/pf_seg_B2.v, pf_seg_B4.v, trim_s.v, pf_seg_B10b_j.v,
   pf_seg_B9_c.v, re-derived on image B's code.

   THE CODE (reac_segconf_parse_file.fuzz_segconf.asan-ubsan.s; 24 instructions walked, 0x88e54 .. 0x88eac and
   0x88efc), with pcs as listing offsets of BASE + AF_reac_segconf_parse_file = 0x87e38:
     0x88e54 lb a0,0(a3)          check B#35 (store4 of c->n): a3 = sh(&c->n) = ((c + 0x2c80) >> 3) + s4, and the
     0x88e58 bnez a0,0x890c0      shadow entry of the block c (pf_obj's sa_addr c SEG_C_SIZE) covers the granule,
                                  so the byte is 0 and the slow arm 0x890c0-0x890d0 is NOT walked (the token
                                  executor's `covered` case; 5 instructions of the slow arm and the error call
                                  0x892dc are dead).
     0x88e5c addi a0,a2,1; 0x88e60 ld a1,88(s1); 0x88e64 sw a0,0(a1)     c->n = n + 1
     0x88e68 bltu s3,a2,0x891c8   UBSan trap T32: s3 = 32 (INV_NEW), a2 = n < 32, so not taken
     0x88e6c li a0,356; 0x88e70 mul a0,a2,a0; 0x88e74 ld a1,56(s1)       a0 = 356 n, a1 = slot 0x38 = ~c
     0x88e78 bltu a1,a0,0x891c8   UBSan trap T33: 2 ^ 64 - 1 - c < 356 n is false, since
                                  c + SEG_C_SIZE <= alloc_ceiling (pb8b_cblk) and n < 32
     0x88e7c ld a1,200(s1); 0x88e80 add s3,a1,a0; 0x88e84 li a2,356; 0x88e88 mv a0,s3; 0x88e8c li a1,0
     0x88e90 jal checked_memset   = pa_sigma SS___asan_memset: seg[n]'s 356 bytes to 0 (hypothesis MEMSET)
     0x88e94 auipc a0 / 0x88e98 addi a2,a0,1196  a2 = "%s" = listing object 35 = 0x21340 (hypothesis OBJ)
     0x88e9c li a1,16; 0x88ea0 mv a0,s3; 0x88ea4 mv a3,s7
     0x88ea8 jal wrapper_snprintf = pa_sigma SS___interceptor_trampoline_snprintf: snprintf(&seg[n], 16, "%s", name)
                                  (hypothesis SNP, stepped by pf_seg_B8b_t.v's pb8b_aj_snprintf_atSF)
     0x88eac j 0x88efc; 0x88efc mv a3,s3; 0x88f00 JOIN
   Counts: 23 instructions 0x88e54-0x88eac + 1 at 0x88efc = 24 walked; check B#35 discharged (covered, no
   obligation and no slow arm); traps T32 and T33 discharged; 2 calls stepped (checked_memset, wrapper_snprintf).

   THE PROOF: three runs of the token executor (lib/B/Prog/SegPaLib.v paj_run_tok / paj_run_to_tok) with the shadow
   entry of the block c, split at the two trap branches by psrr_branch_tok (each refuted from the seed's facts);
   the memset by lib/B/Prog/PaCall.v's aj_intrin_atS at OSet; the snprintf by pf_seg_B8b_t.v's
   pb8b_aj_snprintf_atSF; the FP state the snprintf returns lifted by PaFx.v's srr_apost_baseF_lift, and
   INV_B8B_JOIN rebuilt there with the keep lemmas of lib/B/Prog/pf_seg_B8b_n_k.v (the write set is seg[n], c->n
   and the two callees' stack windows below s1) and the record pb8bn_rconf_new.
   SECTION HYPOTHESES: SNP, MEMSET, OBJ. No SSPX, no VRO (the walk's own keep lemmas carry the image bytes).
   POSITIONAL NAMES: the listing object 35 = 0x21340 = seg_litA_rc F_s (checked by computation in pb8bn_r2, B's
   SegAddr seg_objs), the atom A_OBJ 35 = 276 of the auipc/addi pair; no region letter or STK row of an A table. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs RtPFPf RtPFShared RtPFSx RtPFCmd
RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaRun PaShadow PaJournal SegSyms SegList
SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaSB
PaCall PaCallRun PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c
SegInstB pf_pieces pf_seg_B8b_d pf_seg_B8b_m pf_seg_B8b_t pf_seg_B8b_n_k.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- small tools ---------- *)
Ltac pb8bn_clear_md := repeat match goal with |- context [with_vm_backing (m_vm_lazy ?m) ?x ?m] =>
  let mdv := fresh "mdv" in set (mdv := with_vm_backing (m_vm_lazy m) x m) in *; clearbody mdv end.
Lemma pb8bn_bvr : forall (rr : bvmap 5 word) (r : bv 5) k w, bv_unsigned r = k -> getr rr (Z_to_bv 5 k) = w ->
  getr rr r = w.
Proof. intros rr r k w Hr H. subst k. rewrite Z_to_bv_bv_unsigned in H. exact H. Qed.
Lemma pb8bn_sl : forall rd b L o w, pf_sl rd b L -> In (o, w) L -> rdword rd (b + o) = Some w.
Proof. intros rd b L o w H Hin. exact (proj1 (Forall_forall _ _) H (o, w) Hin). Qed.
(* a register of the state after a run, as the executor wrote it (pf_seg_B2.v pb2_rreg) *)
Ltac pb8bn_rreg HS :=
 lazymatch goal with |- getr (ms_regs ?ms) ?r = _ =>
 lazymatch type of HS with
 | st_ok_pi _ _ ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_pi_restrict_reg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 | st_ok ?sg ?E ?ss (restrict ?Hh ms) =>
  rewrite (st_ok_restrict_reg sg Hh E ss ms r HS);
  let v := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with v
 end end.
(* a register the run kept: its term is its own atom *)
Ltac pb8bn_inS := solve [cbn [In app]; repeat first [left; reflexivity | right]].
Ltac pb8bn_atom HS EE rX R :=
  solve [ pb8bn_rreg HS; rewrite pb8b_den_atom0;
    lazymatch goal with |- ew _ ?k = _ => rewrite (EE k (Z_to_bv 5 (Z.of_nat k)) eq_refl) end;
    apply (pb8b_rg rX _ _ _ R); pb8bn_inS ].

(* ---------- 64-bit words as the executor's terms leave them (trim_k.v's, local copies) ---------- *)
Lemma pb8bn_w64_mod : forall x y, x mod 2 ^ 64 = y mod 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof.
  intros x y H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N]. exact H.
Qed.
Lemma pb8bn_w64_off : forall x c, Z_to_bv 64 (bv_unsigned (Z_to_bv 64 x) + c) = Z_to_bv 64 (x + c).
Proof.
  intros x c. apply pb8bn_w64_mod. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn [Z.of_N].
  rewrite Zplus_mod_idemp_l. reflexivity.
Qed.
Lemma pb8bn_alu_add : forall a b, alu64 ALU_ADD (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a + b).
Proof.
  intros a b. apply bv_eq. rewrite alu64_unsigned, !Z_to_bv_unsigned. cbn [zalu_raw].
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.
Qed.
Lemma pb8bn_md_mul : forall a b, mul_div M_MUL (Z_to_bv 64 a) (Z_to_bv 64 b) = Z_to_bv 64 (a * b).
Proof.
  intros a b. rewrite m_mul. unfold v_mul. apply pb8bn_w64_mod. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. cbn [Z.of_N]. rewrite <- Z.mul_mod by lia. reflexivity.
Qed.
Ltac pb8bn_den :=
  cbn [sv_denot];
  repeat match goal with H : ew ?E ?n = Z_to_bv 64 _ |- context [ew ?E ?n] => rewrite H end;
  rewrite ?pb8bn_w64_off, ?pb8bn_md_mul, ?pb8bn_alu_add;
  unfold w64, seg_spec.rseg_addr, seg_spec.RSEG_SIZE; solve [reflexivity | f_equal; lia].
(* the trap test T33 reads 356 n through the executor's SMd term *)
Lemma pb8bn_U_mul : forall E k (m : nat), ew E k = Z_to_bv 64 (Z.of_nat m) -> (m < 32)%nat ->
  U E (SMd M_MUL (SOff k 0) (SLit 356)) = 356 * Z.of_nat m.
Proof.
intros E k m H Hm. rewrite U_SMd. cbn [zmd_raw].
rewrite (U_atom E k (Z.of_nat m) H ltac:(lia)), U_SLit.
rewrite (zcanon_id 356) by (unfold M64; lia). rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
(* snprintf(d, 16, "%s", s) with s at most 15 bytes and NUL-free: the bytes are s and its NUL *)
Lemma pb8bn_sn : forall (s : list Z), (length s <= 15)%nat ->
  sn_bytes (16 - 1) s = s ++ [0] /\ sn_len (16 - 1) s = Z.of_nat (length s) + 1.
Proof.
intros s Hl. unfold sn_len, sn_bytes. change (Z.to_nat (16 - 1)) with 15%nat.
rewrite firstn_all2 by lia. split; [reflexivity|]. rewrite length_app. cbn [length]. lia.
Qed.
Lemma pb8bn_rg_pres : forall (rX rY : bvmap 5 word) L L', aregs_preserved rX rY -> pf_rg rX L ->
  (forall x, In x L' -> In x L /\ acallee_saved (fst x)) -> pf_rg rY L'.
Proof.
intros rX rY L L' HP H HL. unfold pf_rg in *. rewrite Forall_forall in *.
intros x Hx. destruct (HL x Hx) as [Hin Hcs]. rewrite (HP (fst x) Hcs). exact (H x Hin).
Qed.

(* the seed at NEW (0x88e54): every register its own atom but a3 = sh(&c->n) = ((c + 0x2c80) >> 3) + s4 (atom 32 =
   c, atom 20 = s4 = SHADOW_OFF); the slots 0x38 (~c, atom 33), 0x58 (&c->n), 0xc8 (c) read-only on s1's atom 9;
   c->n's 4 bytes writable on atom 32 *)
Definition pb8bn_shx : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff 32 0x2c80) (SLit 3)) (SOff 20 0).
Definition pb8bn_rs1 : smem :=
  [YP09.mkRegion (Some 9%nat) 0x38 0xd0 0 0
     [YP09.mkChunk 0x38 (CVal 8 (SOff 33 0)); YP09.mkChunk 0x58 (CVal 8 (SOff 32 0x2c80));
      YP09.mkChunk 0xc8 (CVal 8 (SOff 32 0))];
   YP09.mkRegion (Some 32%nat) 0x2c80 0x2c84 0x2c80 0x2c84 []].
Definition pb8bn_G1 : facts := mkFacts [(20%nat, mkAF SB SB 0); (32%nat, mkAF 4096 (2 ^ 47 - 16616) 4)] [] [].
Definition pb8bn_ss0 : sstate := mkSS PF_NEW sr_atoms pb8bn_rs1 None pb8bn_G1.
Definition pb8bn_ss1 : sstate := mkSS PF_NEW (sr_set sr_atoms (Z_to_bv 5 13) pb8bn_shx) pb8bn_rs1 None pb8bn_G1.
Definition pb8bn_Bx : sv := SOff 20 0.
Definition pb8bn_SH : list shent := [mkSHE 32 0 16616].
(* the seed after a call returns: every register its own atom, no region *)
Definition pb8bn_ssR (pc : Z) : sstate := mkSS pc sr_atoms [] None (mkFacts [] [] []).

Section d. Context {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Section e.
Variable B : asyms.
(* the walk's three callee facts *)
Hypothesis SNP : forall fx0 : YK11.FPState,
  @RtFormat.asnprintf_realizes fx0 rc SEGS B (pa_sigma SS___interceptor_trampoline_snprintf) gotwA guardA.
Hypothesis MEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (pa_sigma SS___asan_memset).
Hypothesis OBJ : seg_val_objs (PI := PI).

(* the registers every run of the sub-walk keeps: pf_fi's six, the line's PF_RL / PF_RM, the name in s7 *)
Definition pb8bn_KR (v : pfv) (pos : Z) (o : nat) (ln np : Z) : list (Z * Z) :=
  [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)] ++
  PF_RL v pos ++ PF_RM v o ln ++ [(23, np)].
Ltac pb8bn_incl :=
  let x := fresh "x" in let Hx := fresh "Hx" in
  intros x Hx; unfold pb8bn_KR, PF_RL, PF_RM in Hx; cbn [In app] in Hx;
  repeat (destruct Hx as [<- | Hx];
    [split; [unfold pb8bn_KR, PF_RL, PF_RM; pb8bn_inS | unfold acallee_saved; cbn [fst]; lia] |]);
  destruct Hx.

Lemma pb8bn_rom_view : forall (W : world SEGS) mem,
  arodata_okP SEGS RLO_A RHI_A B (rdW W mem) -> rt_rom_view SEGS B W mem.
Proof.
intros W mem H a (sg & Hsg & Hw & Hr) Ho He.
exact (H a (or_introl (ex_intro _ sg (conj Hsg (conj Hw Hr)))) Ho He).
Qed.

(* pf_base at a later state: the journal there, the kept bytes, the six kept registers, the rounding mode *)
Lemma pb8bn_base_move : forall (fx0 fx1 : YK11.FPState) v pos n lyc Sc (Wc : world SEGS) rX memc mdc rX' memc'
  mdc' sc,
  pb8bn_G v pos n -> pb8bn_kept v n (rdW Wc memc) (rdW Wc memc') ->
  pf_base (fx := fx0) B v pos lyc Sc Wc rX memc mdc sc ->
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc' mdc' 0 ->
  @sa_frm0 fx1 ->
  pf_rg rX' [(2, pf_s1 v); (3, as_gp B); (4, as_tp B); (8, pf_sp0 v); (9, pf_s1 v); (20, SHADOW_OFF)] ->
  pf_base (fx := fx1) B v pos lyc Sc Wc rX' memc' mdc' sc.
Proof.
intros fx0 fx1 v pos n lyc Sc Wc rX memc mdc rX' memc' mdc' sc G KK HB HJ' HFRM HRG.
pose proof HB as (HCX & HFI & HOBJ & HSL & HFSH).
pose proof HFI as (_ & Hly & HSc & HPERM & HSAV & HFLAG & _ & HTF & HC8 & _).
split; [exact HCX|].
split.
{ split; [exact HJ'|]. split; [exact Hly|]. split; [exact HSc|]. split; [exact HPERM|].
  split; [eapply pb8bn_k_saved; eassumption|].
  split; [eapply pb8bn_k_flag; eassumption|].
  split; [exact HFRM|]. split; [exact HTF|].
  split.
  { eapply pb8bn_k_sl; try eassumption.
    apply Forall_forall. intros ov Hov. cbn [In] in Hov.
    repeat (destruct Hov as [<- | Hov]; [cbn [fst]; lia|]). destruct Hov. }
  exact HRG. }
split; [eapply pb8bn_k_obj; eassumption|].
split; [eapply pb8bn_k_sl; try eassumption; apply pb8bn_PF_SL_offs|].
eapply pb8bn_k_fsh; eassumption.
Qed.

Section x1. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.
Let RUN := paj_run B LAWS.
Let RUNTO := paj_run_to B LAWS.
Let BR := paj_branch (PI := PI).

Lemma pb8bn_seed1 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name,
  INV_NEW B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 (p_c v); w64 (pf_nt (p_c v))])) pb8bn_ss1
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_NEW)) memc (seg_rom SEGS))).
Proof.
intros n0 v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HI.
destruct HI as (HBASE & _ & _ & _ & _ & _ & _ & HN32 & HRG).
pose proof HBASE as (HCX & HFI & HOBJ & HSL & _).
destruct (pb8b_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (Hc0 & Hc16 & Hc4 & Hcc & HCA & HCH & Hap).
pose proof HFI as (HJ & _ & _ & _ & _ & _ & _ & _ & HC8 & HRG0).
pose proof asan_consts as (C1 & _). pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
unfold seg_spec.SEG_C_SIZE in Hcc.
destruct HCH as (b & m & Hb & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & Hcl & Happ & Hbp & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
set (E := Eimg (Ereg rX [w64 (p_c v); w64 (pf_nt (p_c v))])).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 (p_c v))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pf_nt (p_c v)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (R9 : getr rX (Z_to_bv 5 9) = w64 (pf_s1 v)) by (apply (pb8b_rg rX _ 9 _ HRG0); pb8b_in).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (pb8b_rg rX _ 20 _ HRG0); pb8b_in).
assert (R13 : getr rX (Z_to_bv 5 13) = w64 (shadow_addr (p_c v + seg_spec.RC_N)))
  by (apply (pb8b_rg rX _ 13 _ HRG); pb8b_in).
assert (E20 : ew E 20 = Z_to_bv 64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20).
assert (U9 : bv_unsigned (ew E 9) = pf_s1 v)
  by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = p_c v) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite E20; unfold SHADOW_OFF; apply unsigned_lit_small; lia).
assert (W38 : rdword (rdW Wc memc) (pf_s1 v + 0x38) = Some (pf_nt (p_c v))) by (apply (pb8bn_sl _ _ _ _ _ HSL); pb8b_in).
assert (W58 : rdword (rdW Wc memc) (pf_s1 v + 0x58) = Some (p_c v + seg_spec.RC_N)) by (apply (pb8bn_sl _ _ _ _ _ HSL); pb8b_in).
assert (WC8 : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v)) by (apply (pb8bn_sl _ _ _ _ _ HC8); pb8b_in).
rewrite restrict_mkst_fx.
assert (HS0 : st_ok_pi SEGS VAL E pb8bn_ss0
  (mkst rX (Z_to_bv 64 (BASE + PF_NEW)) (mrestrict (w_H Wc) memc) (seg_rom SEGS))).
{ unfold pb8bn_ss0. apply pa_entry_st_ok_full.
  - subst E. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold pb8bn_rs1. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite U9. split; [lia|]. split; [lia|]. split; [intros o' Ho'; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x38 8 (SOff 33 0) (pf_nt (p_c v))).
        -- rewrite pb8b_den_atom0. exact E33.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold pf_nt. lia.
        -- cbn; lia.
        -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W38).
      * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0x58 8 (SOff 32 0x2c80) (p_c v + seg_spec.RC_N)).
        -- exact (pb8b_den_off E 32 (p_c v) 0x2c80 E32 ltac:(lia)).
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). unfold seg_spec.RC_N, seg_spec.SEG_C_SIZE in *. lia.
        -- cbn; lia.
        -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ W58).
      * apply (chunk_ok_val SEGS E _ (pf_s1 v) 0xc8 8 (SOff 32 0) (p_c v)).
        -- rewrite pb8b_den_atom0. exact E32.
        -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
        -- cbn; lia.
        -- exact (val_mem_of_rdword SEGS (w_H Wc) memc _ _ WC8).
    + rewrite U32. split; [lia|]. split; [lia|]. split; [|constructor].
      intros o' Ho'. apply (apresent_writable SEGS). apply (proj1 (Hbp (p_c v + o') ltac:(unfold seg_spec.SEG_C_SIZE in *; lia))).
  - unfold pb8bn_rs1. apply pairwise_disjoint_of_extents. unfold extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U9, U32.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
  - unfold pb8bn_G1. split; [|split; exact I].
    cbn [f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U20, U32. change (2 ^ 4) with 16. rewrite Z.pow_0_r, Z.mod_1_r.
    unfold SB, SHADOW_OFF, seg_spec.SEG_C_SIZE in *. repeat split; lia. }
assert (HR13 : getr (ms_regs (mkst rX (Z_to_bv 64 (BASE + PF_NEW)) (mrestrict (w_H Wc) memc) (seg_rom SEGS)))
  (Z_to_bv 5 13) = sv_denot E pb8bn_shx).
{ cbn [ms_regs mkst]. rewrite R13. unfold pb8bn_shx.
  rewrite (denot_shx E 32 20 0x2c80 (p_c v) SHADOW_OFF E32 E20) by (unfold SHADOW_OFF; lia).
  unfold w64, shadow_addr, seg_spec.RC_N. reflexivity. }
pose proof (st_ok_pi_set_reg E pb8bn_ss0 _ (Z_to_bv 5 13) pb8bn_shx HS0
  ltac:(intros Hq; apply (f_equal bv_unsigned) in Hq; vm_compute in Hq; discriminate) HR13) as HS1.
exact HS1.
Qed.

(* ---------- R1: NEW (0x88e54) .. the memset call (0x88e90) ---------- *)
Lemma pb8bn_r1 : forall n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name (Q : world SEGS -> config -> Prop),
  INV_NEW B n v pos lyc Sc Wc rX memc mdc cf nm o ln d np name ->
  (forall rX1 memc1 mdc1,
     ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
       (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc1 mdc1 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (p_c v + seg_spec.RC_N <= a < p_c v + seg_spec.RC_N + 4) ->
        rdW Wc memc1 a = rdW Wc memc a) ->
     (forall k, (k < 4)%nat -> rdW Wc memc1 (p_c v + seg_spec.RC_N + Z.of_nat k) =
        Some (le_byte (Z.of_nat (length (rc_seg cf)) + 1) 4 k)) ->
     pf_rg rX1 (pb8bn_KR v pos o ln np ++
        [(19, seg_spec.rseg_addr (p_c v) (length (rc_seg cf)));
         (10, seg_spec.rseg_addr (p_c v) (length (rc_seg cf))); (11, 0); (12, 356); (1, BASE + 16596)]) ->
     SRr SEGS Wc (mkCfg (mkst rX1 (Z_to_bv 64 (pa_sigma SS___asan_memset)) memc1 (seg_rom SEGS)) mdc1) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_NEW) rX memc mdc) Q.
Proof.
intros n0 v pos lyc Sc Wc rX memc mdc cf nm o ln d np name Q HI Kc.
pose proof (pb8bn_seed1 n0 v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HI) as HS.
destruct HI as (HBASE & HMID & HST & HSTR & HINB & HLEN & HFIND & HN32 & HRG).
pose proof HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
set (n := length (rc_seg cf)) in *.
pose proof (pb8bn_G_of B v pos lyc Sc Wc rX memc mdc n HCX HFI HOBJ HN32) as G.
destruct (pb8b_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (Hc0 & Hc16 & Hc4 & Hcc & HCA & HCH & Hap).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
pose proof asan_consts as (C1 & _). pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
unfold seg_spec.SEG_C_SIZE in Hcc.
destruct HCH as (b & m & Hb & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & Hcl & Happ & Hbp & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
set (E := Eimg (Ereg rX [w64 (p_c v); w64 (pf_nt (p_c v))])) in HS.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew E k = getr rX r)
  by (intros k r Hk; subst E; apply ew_Eimg_Ereg_nat; exact Hk).
assert (E32 : ew E 32 = Z_to_bv 64 (p_c v))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (pf_nt (p_c v)))
  by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (R20 : getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF) by (apply (pb8b_rg rX _ 20 _ HRG0); pb8b_in).
assert (U32 : bv_unsigned (ew E 32) = p_c v) by (rewrite E32; apply unsigned_lit_small; lia).
assert (HRA : range_addressable (rdW Wc memc) SHADOW_OFF (p_c v) 16616)
  by (destruct HCA as (_ & _ & _ & H & _); exact H).
pose proof (pb8b_rg rX _ 19 32 HRG ltac:(pb8b_in)) as R19.
pose proof (pb8b_rg rX _ 12 _ HRG ltac:(pb8b_in)) as R12.
revert HS HEI EE E32 E33 U32. generalize E as E0. clear E. intros E0 HS HEI EE E32 E33 U32.
assert (E19 : ew E0 19 = Z_to_bv 64 32) by (rewrite (EE 19%nat (Z_to_bv 5 19) eq_refl); exact R19).
assert (E12 : ew E0 12 = Z_to_bv 64 (Z.of_nat n)) by (rewrite (EE 12%nat (Z_to_bv 5 12) eq_refl); exact R12).
assert (UB : U E0 pb8bn_Bx = SHADOW_OFF).
{ unfold pb8bn_Bx. rewrite (U_atom E0 20 SHADOW_OFF); [reflexivity | rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); exact R20 |].
  unfold SHADOW_OFF; lia. }
assert (UC : U E0 (SOff 32 0) = p_c v) by (apply U_atom; [exact E32 | lia]).
assert (SHOK : sh_ok SEGS pb8bn_Bx pb8bn_SH E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, pb8bn_SH. apply Forall_cons; [|apply Forall_nil].
  eapply (shent_ok_of_range SEGS (w_H Wc) memc E0 pb8bn_Bx 32%nat (p_c v) 16616 (p_c v) 0 16616 HRA UB UC); [lia | lia |].
  intros x Hx. change (Z.min 0 16616) with 0 in Hx. change (Z.max 0 16616) with 16616 in Hx.
  pose proof G as (_ & _ & _ & _ & HappC & _). unfold in_app, seg_spec.SEG_C_SIZE, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, SHADOW_OFF in *.
  lia. }
unfold cfg_at. change (w64 (BASE + PF_NEW)) with (Z_to_bv 64 (BASE + PF_NEW)).
(* 0x88e54 .. 0x88e64: check B#35 (covered), c->n = n + 1 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - apply pb8b_fp_block; unfold seg_spec.RC_N; lia.
  - exists b, m. split; [exact Hb | unfold seg_spec.SEG_C_SIZE in *; lia]. }
assert (K1 : forall a, 0 <= a < 2 ^ 64 -> ~ (p_c v + seg_spec.RC_N <= a < p_c v + seg_spec.RC_N + 4) ->
    rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha Hn.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) memc (ms_mem ms)
      (fun a => p_c v + seg_spec.RC_N <= a < p_c v + seg_spec.RC_N + 4) HFr); [|exact Ha | exact Hn] end.
  intros bb wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U32 in Hrr;
    unfold seg_spec.RC_N; lia |]). destruct Hin'. }
clear HF HFr HG.
(* 0x88e68 `bltu s3,a2`: trap T32 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U in Hc.
  rewrite (U_atom E0 19 32 E19) in Hc by lia. rewrite (U_atom E0 12 (Z.of_nat n) E12) in Hc by lia.
  apply Z.ltb_lt in Hc. lia. }
clear Hc.
(* 0x88e6c .. 0x88e74 *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - apply pb8b_fp_block; unfold seg_spec.RC_N; lia.
  - exists b, m. split; [exact Hb | unfold seg_spec.SEG_C_SIZE in *; lia]. }
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (p_c v + seg_spec.RC_N <= a < p_c v + seg_spec.RC_N + 4) ->
    rdW Wc (ms_mem ms0) a = rdW Wc (ms_mem ms) a).
{ intros a Ha Hn.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms) (ms_mem ms0)
      (fun a => p_c v + seg_spec.RC_N <= a < p_c v + seg_spec.RC_N + 4) HFr); [|exact Ha | exact Hn] end.
  intros bb wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U32 in Hrr;
    unfold seg_spec.RC_N; lia |]). destruct Hin'. }
clear HF HFr HG.
(* 0x88e78 `bltu a1,a0`: trap T33 *)
psrr_branch_tok RUN BR HS SHOK Bspan.
{ exfalso. rewrite branch_ltu_U in Hc.
  rewrite (U_atom E0 33 (pf_nt (p_c v)) E33) in Hc by (unfold pf_nt; lia).
  rewrite (pb8bn_U_mul E0 12 n E12 HN32) in Hc.
  apply Z.ltb_lt in Hc. unfold pf_nt in Hc. lia. }
clear Hc.
(* 0x88e7c .. 0x88e90: s3 = &seg[n], the memset call *)
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_cons_ro; [cbn; lia|].
  eapply awr_ok_cons_gen; [reflexivity | exact U32 | | apply awr_ok_nil].
  intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
  - apply pb8b_fp_block; unfold seg_spec.RC_N; lia.
  - exists b, m. split; [exact Hb | unfold seg_spec.SEG_C_SIZE in *; lia]. }
assert (K3 : forall a, 0 <= a < 2 ^ 64 -> ~ (p_c v + seg_spec.RC_N <= a < p_c v + seg_spec.RC_N + 4) ->
    rdW Wc (ms_mem ms1) a = rdW Wc (ms_mem ms0) a).
{ intros a Ha Hn.
  lazymatch type of HFr with frame_of ?Ex ?rs _ _ =>
    apply (kept_of_frame (segs := SEGS) Ex rs (w_H Wc) (ms_mem ms0) (ms_mem ms1)
      (fun a => p_c v + seg_spec.RC_N <= a < p_c v + seg_spec.RC_N + 4) HFr); [|exact Ha | exact Hn] end.
  intros bb wlo whi a' Hin' Hrr. vm_compute in Hin'. cbv beta.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U32 in Hrr;
    unfold seg_spec.RC_N; lia |]). destruct Hin'. }
(* c->n's 4 bytes, read back from the region the run wrote *)
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1 end.
cbn [ms_mem restrict] in HR1.
pose proof (field_of_region_any (segs := SEGS) E0 _ 32 (p_c v) _ _ _ _ _ 11392 4 (SOff 12 1) HR1 U32
  ltac:(pb8b_in) ltac:(cbn; lia)) as HV.
change (N.to_nat 4) with 4%nat in HV. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32) in HV.
rewrite (pb8b_den_off E0 12 (Z.of_nat n) 1 E12 ltac:(lia)) in HV.
rewrite unsigned_lit_small in HV by lia. rewrite Z.mod_small in HV by lia.
pmkst HS.
apply Kc.
- exact HJ.
- intros a Ha Hn. rewrite (K3 a Ha Hn), (K2 a Ha Hn). exact (K1 a Ha Hn).
- intros k Hk. unfold aview.
  replace (p_c v + seg_spec.RC_N + Z.of_nat k) with (p_c v + 11392 + Z.of_nat k) by (unfold seg_spec.RC_N; lia).
  rewrite (HV k Hk). cbn [option_map]. rewrite pb8bn_bv8; [reflexivity|].
  unfold le_byte. apply Z.mod_pos_bound. lia.
- unfold pf_rg, pb8bn_KR, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    first [ pb8bn_atom HS EE rX HRG0 | pb8bn_atom HS EE rX HRG
          | solve [pb8bn_rreg HS; exact (codeptr_val E0 16596 HEI)]
          | solve [pb8bn_rreg HS; pb8bn_den] ].
Qed.

(* ---------- R2: the memset return (0x88e94) .. the snprintf call (0x88ea8) ---------- *)
Lemma pb8bn_r2 : forall v pos lyc Sc Wc o ln np ds (rX : bvmap 5 word) memc mdc (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 ->
  pf_rg rX (pb8bn_KR v pos o ln np ++ [(19, ds)]) ->
  (forall rX3 memc3 mdc3,
     ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
       (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc3 mdc3 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc3 a = rdW Wc memc a) ->
     pf_rg rX3 (pb8bn_KR v pos o ln np ++ [(19, ds); (10, ds); (11, 16); (12, seg_litA_rc F_s); (13, np);
       (1, BASE + 16620)]) ->
     SRr SEGS Wc (mkCfg (mkst rX3 (Z_to_bv 64 (pa_sigma SS___interceptor_trampoline_snprintf)) memc3
       (seg_rom SEGS)) mdc3) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_B8B_RET_MEMSET) rX memc mdc) Q.
Proof.
intros v pos lyc Sc Wc o ln np ds rX memc mdc Q HJ HRG Kc.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (pb8bn_ssR PF_B8B_RET_MEMSET)
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_B8B_RET_MEMSET)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pb8bn_ssR. apply pa_entry_st_ok_full;
    [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
revert HS HEI EE. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI EE.
assert (SHOK : sh_ok SEGS pb8bn_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + PF_B8B_RET_MEMSET)) with (Z_to_bv 64 (BASE + PF_B8B_RET_MEMSET)).
paj_run_tok RUN HS HJ SHOK Bspan.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_nil. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros bb wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
pmkst HS.
apply Kc; [exact HJ | exact KM |].
unfold pf_rg, pb8bn_KR, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  first [ pb8bn_atom HS EE rX HRG
        | solve [pb8bn_rreg HS; exact (codeptr_val E 16620 HEI)]
        | solve [pb8bn_rreg HS;
            rewrite pb8b_den_atom0, (img_env_atomP E 276%nat HEI) by (unfold A_TEXT, A_LIM; lia);
            change 276%nat with (A_OBJ 35); rewrite (OBJ 35%nat ltac:(apply Nat.ltb_lt; vm_compute; reflexivity));
            unfold w64; f_equal; vm_compute; reflexivity]
        | solve [pb8bn_rreg HS; pb8bn_den] ].
Qed.

(* ---------- R3: the snprintf return (0x88eac) .. JOIN (0x88f00) ---------- *)
Lemma pb8bn_r3 : forall v pos lyc Sc Wc o ln np ds (rX : bvmap 5 word) memc mdc (Q : world SEGS -> config -> Prop),
  ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
    (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc mdc 0 ->
  pf_rg rX (pb8bn_KR v pos o ln np ++ [(19, ds)]) ->
  (forall rX5 memc5 mdc5,
     ajournal SEGS B STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v)
       (p_mem v) (p_md v) [(5, pos)] lyc Sc Wc memc5 mdc5 0 ->
     (forall a, 0 <= a < 2 ^ 64 -> rdW Wc memc5 a = rdW Wc memc a) ->
     pf_rg rX5 (pb8bn_KR v pos o ln np ++ [(19, ds); (13, ds)]) ->
     SRr SEGS Wc (cfg_at SEGS (BASE + PF_B8B_JOIN) rX5 memc5 mdc5) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + PF_B8B_RET_SNPN) rX memc mdc) Q.
Proof.
intros v pos lyc Sc Wc o ln np ds rX memc mdc Q HJ HRG Kc.
assert (HS : st_ok_pi SEGS VAL (Eimg (Ereg rX [])) (pb8bn_ssR PF_B8B_RET_SNPN)
  (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + PF_B8B_RET_SNPN)) memc (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold pb8bn_ssR. apply pa_entry_st_ok_full;
    [apply regs_ok_Eimg_Ereg | vm_compute; reflexivity | constructor | cbn; tauto | split; [exact I | split; exact I]]. }
assert (HEI : img_env VAL A_LIM (Eimg (Ereg rX []))) by apply Eimg_env.
assert (EE : forall k (r : bv 5), Z.of_nat k = bv_unsigned r -> ew (Eimg (Ereg rX [])) k = getr rX r)
  by (intros k r Hk; apply ew_Eimg_Ereg_nat; exact Hk).
revert HS HEI EE. generalize (Eimg (Ereg rX [])) as E. intros E HS HEI EE.
assert (SHOK : sh_ok SEGS pb8bn_Bx [] E (mrestrict (w_H Wc) memc)) by constructor.
unfold cfg_at. change (w64 (BASE + PF_B8B_RET_SNPN)) with (Z_to_bv 64 (BASE + PF_B8B_RET_SNPN)).
paj_run_to_tok RUNTO HS HJ SHOK Bspan PF_B8B_JOIN.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc fr0 lyx own) end.
  apply awr_ok_nil. }
assert (KM : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros bb wlo whi a' Hin' Hrr. vm_compute in Hin'. destruct Hin'. }
pmkst HS.
lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg (Z_to_bv 64 (_ + ?k)) ?mm ?rom) ?mdx) _ =>
  change (mkCfg (mkst rg (Z_to_bv 64 (BASE + k)) mm rom) mdx) with (cfg_at SEGS (BASE + PF_B8B_JOIN) rg mm mdx) end.
apply Kc; [exact HJ | exact KM |].
unfold pf_rg, pb8bn_KR, PF_RL, PF_RM. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  pb8bn_atom HS EE rX HRG.
Qed.
End x1.

(* ---------- the sub-walk NEW -> JOIN ---------- *)
Section x2. Context {fx : YK11.FPState}.
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

Theorem pb8b_new_holds : forall n, HA_B8B_JOIN B n -> H_NEW B n.
Proof.
intros n0 JOIN v pos lyc Sc Wc rX memc mdc cf nm o ln d np name HI.
pose proof HI as (HBASE & HMID & HST & HSTR & HINB & HLEN & HFIND & HN32 & HRG).
pose proof HBASE as (HCX & HFI & HOBJ & HSL & HFSH).
rewrite (pb8b_step_new cf nm name (ln + 1) HFIND HN32).
set (n := length (rc_seg cf)) in *.
pose proof (pb8bn_G_of B v pos lyc Sc Wc rX memc mdc n HCX HFI HOBJ HN32) as G.
destruct (pb8b_geo B v pos lyc Sc Wc rX memc mdc HCX HFI) as (HGEO & Hin & EF & Hfrs & HAR).
destruct (pb8b_cblk B v pos lyc Sc Wc rX memc mdc HCX HFI HOBJ) as (Hc0 & Hc16 & Hc4 & Hcc & HCA & HCH & Hap).
pose proof HFI as (HJ & Hly & HSc & HPERM & HSAV & HFLAG & HFRM & HTF & HC8 & HRG0).
pose proof asan_consts as (C1 & _). pose proof HCX as (_ & _ & _ & Hc64 & _).
pose proof HGEO as (S1 & S2 & S3 & S4 & S5 & S6 & F1 & F2 & F3 & F4 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _).
pose proof pf_B_values as (_ & _ & _ & EGW & EGD & _ & _ & _ & _ & _ & EFs).
pose proof G as (_ & _ & _ & _ & HappC & HoffC & _).
unfold seg_spec.SEG_C_SIZE in Hcc.
destruct HCH as (b & m & Hb & Hb1 & Hb2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc b m HAR Hb) as (_ & _ & Hcl & Happ & Hbp & _ & Hm0).
pose proof (req_size_pos m ltac:(lia)) as [_ Hrm].
unfold seg_spec.SEG_C_SIZE in Hb2.
pose proof HST as (HRC & HNM & HCNT).
pose proof HMID as (Ho & Hk & HCTX).
pose proof HINB as (Hnp1 & Hnp2). unfold PF_O_BUF in Hnp1, Hnp2.
pose proof HSTR as ((_ & Hnz) & _).
pose proof (pb8b_bytes_range_aview SEGS (w_H Wc) memc np name HSTR) as Hrng0.
assert (Hrng : Forall (fun z => 0 <= z < 256) name) by (eapply Forall_impl; [|exact Hrng0]; cbv beta; intros; lia).
set (ds := seg_spec.rseg_addr (p_c v) n).
assert (Hds : p_c v <= ds /\ ds + 356 <= p_c v + 0x2c80).
{ subst ds. unfold seg_spec.rseg_addr, seg_spec.RSEG_SIZE. lia. }
assert (Ho16 : (pf_s1 v - pf_sp0 v) mod 16 = 0) by exact (pb8b_m16 _ _ S6 S3).
destruct (pb8bn_sn name ltac:(lia)) as (Esb & Esl).
(* ---- R1 ---- *)
apply (pb8bn_r1 n0 v pos lyc Sc Wc rX memc mdc cf nm o ln d np name _ HI).
intros rX1 memc1 mdc1 HJ1 K1 CN1 RG1.
fold n in RG1. fold ds in RG1.
assert (Esp1 : spZ rX1 = pf_s1 v).
{ unfold spZ. rewrite (pb8bn_bvr rX1 (2%bv : bv 5) 2 (w64 (pf_s1 v)) eq_refl
    ltac:(apply (pb8b_rg rX1 _ _ _ RG1); pb8bn_inS)).
  unfold w64. apply unsigned_lit_small. lia. }
assert (KK1 : pb8bn_kept v n (rdW Wc memc) (rdW Wc memc1)).
{ intros a Ha Hw. apply K1; [exact Ha|]. intros Hc'. apply Hw. right; left. exact Hc'. }
pose proof (proj1 HJ1) as HAR1.
assert (HCA1 : sa_addr (rdW Wc memc1) (p_c v) seg_spec.SEG_C_SIZE).
{ eapply pb8bn_k_addr; try eassumption; unfold seg_spec.SEG_C_SIZE, kHighMemEnd; lia. }
(* ---- the memset 0x88e90 ---- *)
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (pa_sigma SS___asan_memset) (MEMSET fx) Wc rX1 memc1
    STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v)
    [(5, pos)] lyc Sc mdc1 0 ds 0 356 (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + 16596)) HJ1).
  - apply (pb8bn_bvr _ _ 10); [reflexivity | apply (pb8b_rg rX1 _ _ _ RG1); pb8bn_inS].
  - apply (pb8bn_bvr _ _ 11); [reflexivity | apply (pb8b_rg rX1 _ _ _ RG1); pb8bn_inS].
  - apply (pb8bn_bvr _ _ 12); [reflexivity | apply (pb8b_rg rX1 _ _ _ RG1); pb8bn_inS].
  - lia.
  - lia.
  - lia.
  - rewrite Esp1. lia.
  - exact Ho16.
  - lia.
  - rewrite ESTK. unfold ESTACK. lia.
  - apply (pb8bn_bvr _ _ 3); [reflexivity | apply (pb8b_rg rX1 _ _ _ RG1); pb8bn_inS].
  - apply (pb8bn_bvr _ _ 4); [reflexivity | apply (pb8b_rg rX1 _ _ _ RG1); pb8bn_inS].
  - apply (pb8bn_bvr _ _ 1); [reflexivity | apply (pb8b_rg rX1 _ _ _ RG1); pb8bn_inS].
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [right; left; split|].
    + apply pb8b_fp_block; unfold seg_spec.RC_N; lia.
    + exists b, m. split; [exact Hb | lia].
    + unfold ESTACK. lia.
  - intros a Ha _ [[_ Hi'] | Hs']; [exfalso | lia].
    exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc b m a HAR Hb ltac:(lia) Hi').
  - apply amem_range_high; [lia | | lia]. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.SEG_C_SIZE in HappC. lia.
  - destruct HCA1 as (_ & _ & _ & HRA1 & _).
    exact (range_addressable_sub _ _ _ _ ds 356 HRA1 ltac:(unfold seg_spec.SEG_C_SIZE; lia)
      ltac:(unfold seg_spec.SEG_C_SIZE; lia)).
  - intros _. destruct HCA1 as (_ & _ & _ & _ & HHV1).
    exact (pb8bn_hull_sub _ _ _ ds 356 (HHV1 ltac:(unfold seg_spec.SEG_C_SIZE; lia)) ltac:(lia) ltac:(lia)
      ltac:(unfold seg_spec.SEG_C_SIZE; lia)).
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & H10a & HZ2 & HK2 & HPR2 & HSM2).
assert (HZ2' : forall i, 0 <= i < 356 -> rdW Wc mem2 (ds + i) = Some 0)
  by (intros i Hi; rewrite (HZ2 i Hi); reflexivity).
change (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + 16596)) mem2 (seg_rom SEGS)) md2)
  with (cfg_at SEGS (BASE + PF_B8B_RET_MEMSET) regs2 mem2 md2).
(* ---- R2 ---- *)
apply (pb8bn_r2 v pos lyc Sc Wc o ln np ds regs2 mem2 md2 _ HJ2).
{ apply (pb8bn_rg_pres rX1 regs2 _ _ HP2 RG1). pb8bn_incl. }
intros rX3 memc3 mdc3 HJ3 K3 RG3.
assert (KK3 : pb8bn_kept v n (rdW Wc memc) (rdW Wc memc3)).
{ intros a Ha Hw. unfold pb8bn_Wr in Hw. fold ds in Hw. rewrite (K3 a Ha).
  rewrite (HK2 a Ha) by (unfold ESTACK in *; lia).
  apply K1; [exact Ha | lia]. }
pose proof (proj1 HJ3) as HAR3.
assert (HCA3 : sa_addr (rdW Wc memc3) (p_c v) seg_spec.SEG_C_SIZE).
{ eapply pb8bn_k_addr; try eassumption; unfold seg_spec.SEG_C_SIZE, kHighMemEnd; lia. }
assert (HOBJ3 : pf_obj B v lyc Sc (rdW Wc memc3)) by (eapply pb8bn_k_obj; eassumption).
assert (HFSH3 : pf_fsh (rdW Wc memc3) (pf_SH v pos) PF_SC_LINE) by (eapply pb8bn_k_fsh; eassumption).
assert (HSTR3 : sa_str (rdW Wc memc3) np name) by (eapply pb8bn_k_buf; eassumption).
pose proof (pb8bn_addr_buf v pos _ np (Z.of_nat (length name) + 1) HGEO HFSH3 ltac:(unfold PF_O_BUF; lia)
  ltac:(lia) ltac:(unfold PF_O_BUF; lia)) as HNA3.
pose proof HOBJ3 as (_ & _ & _ & _ & _ & _ & HLIT3 & HROD3 & HSSP3).
pose proof (HLIT3 F_s ltac:(unfold PARSE_FILE_LITS; apply in_or_app; left; left; reflexivity)) as HFS3.
pose proof HFS3 as (_ & HFSS3 & HFSP3 & _).
assert (HFSA3 : sa_addr (rdW Wc memc3) (seg_litA_rc F_s) 3).
{ pose proof (HFSP3 lyc Sc Wc memc3 mdc3 HAR3) as X. rewrite pb8b_F_s_len in X. exact X. }
assert (Esp3 : spZ rX3 = pf_s1 v).
{ unfold spZ. rewrite (pb8bn_bvr rX3 (2%bv : bv 5) 2 (w64 (pf_s1 v)) eq_refl
    ltac:(apply (pb8b_rg rX3 _ _ _ RG3); pb8bn_inS)).
  unfold w64. apply unsigned_lit_small. lia. }
assert (Hspan : seg_spec.cstr_span np name <= Z.of_nat (length name) + 8).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (np + Z.of_nat (length name) + 1)) 8 ltac:(lia)). lia. }
assert (Hspan0 : 0 <= seg_spec.cstr_span np name).
{ unfold seg_spec.cstr_span. pose proof (Z.mod_pos_bound (- (np + Z.of_nat (length name) + 1)) 8 ltac:(lia)). lia. }
(* ---- the snprintf 0x88ea8 ---- *)
eapply SRr_bind.
{ apply (pb8b_aj_snprintf_atSF (fx := fx) SEGS B LAWS pa_segs_low gotwA guardA
    (pa_sigma SS___interceptor_trampoline_snprintf) (SNP fx) Wc rX3 memc3 STK_reac_segconf_parse_file (pf_sp0 v)
    (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v) [(5, pos)] lyc Sc mdc3 0 ds 16
    (seg_litA_rc F_s) name (pf_s1 v - pf_sp0 v) (Z_to_bv 64 (BASE + 16620)) HJ3).
  - apply (pb8bn_bvr _ _ 10); [reflexivity | apply (pb8b_rg rX3 _ _ _ RG3); pb8bn_inS].
  - apply (pb8bn_bvr _ _ 11); [reflexivity | apply (pb8b_rg rX3 _ _ _ RG3); pb8bn_inS].
  - apply (pb8bn_bvr _ _ 12); [reflexivity | apply (pb8b_rg rX3 _ _ _ RG3); pb8bn_inS].
  - lia.
  - lia.
  - lia.
  - rewrite Esp3. lia.
  - exact Ho16.
  - lia.
  - rewrite ESTK. unfold CMD_SNP_K, ESTACK. lia.
  - apply (pb8bn_bvr _ _ 3); [reflexivity | apply (pb8b_rg rX3 _ _ _ RG3); pb8bn_inS].
  - apply (pb8bn_bvr _ _ 4); [reflexivity | apply (pb8b_rg rX3 _ _ _ RG3); pb8bn_inS].
  - apply (pb8bn_bvr _ _ 1); [reflexivity | apply (pb8b_rg rX3 _ _ _ RG3); pb8bn_inS].
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a Ha. split; [right; left; split|].
    + apply pb8b_fp_block; unfold seg_spec.RC_N; lia.
    + exists b, m. split; [exact Hb | lia].
    + unfold CMD_SNP_K, ESTACK. lia.
  - intros a Ha _ [[_ Hi'] | Hs']; [exfalso | lia].
    exact (blk_img SEGS B LAWS lyc Sc Wc memc mdc b m a HAR Hb ltac:(lia) Hi').
  - apply amem_range_high; [lia | | lia]. unfold in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL, seg_spec.SEG_C_SIZE in HappC. lia.
  - destruct HCA3 as (_ & _ & _ & HRA3 & _).
    exact (range_addressable_sub _ _ _ _ ds 16 HRA3 ltac:(unfold seg_spec.SEG_C_SIZE; lia)
      ltac:(unfold seg_spec.SEG_C_SIZE; lia)).
  - destruct HCA3 as (_ & _ & _ & _ & HHV3).
    exact (pb8bn_hull_sub _ _ _ ds 16 (HHV3 ltac:(unfold seg_spec.SEG_C_SIZE; lia)) ltac:(lia) ltac:(lia)
      ltac:(unfold seg_spec.SEG_C_SIZE; lia)).
  - rewrite Esl. unfold off_img, seg_spec.SEG_C_SIZE in HoffC |- *. lia.
  - unfold CMD_IMG_HI, CMD_SNP_K, ESTACK, kImgEnd. lia.
  - exact HSSP3.
  - unfold gotwA. lia.
  - unfold gotwA, CMD_IMG_HI, kImgEnd. lia.
  - unfold guardA. lia.
  - unfold guardA, CMD_IMG_HI, kImgEnd. lia.
  - unfold gotwA, CMD_IMG_LO. lia.
  - unfold guardA, CMD_IMG_LO. lia.
  - apply (pb8b_FR_s_regs _ _ (seg_litA_rc F_s) np name rX3).
    + unfold argZ. change (Z_to_bv 5 (10 + 3)) with (Z_to_bv 5 13).
      rewrite (pb8b_rg rX3 _ 13 np RG3 ltac:(pb8b_in)). unfold w64. apply unsigned_lit_small. lia.
    + lia.
    + unfold CMD_IMG_LO. lia.
    + unfold CMD_GOTW. lia.
    + exact HFSS3.
    + exact HFSA3.
    + unfold snp_out. rewrite Esp3, Esl. unfold off_img, seg_spec.SEG_C_SIZE in HoffC.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint;
        cbn [fst snd]; unfold CMD_SNP_K, ESTACK; lia.
    + lia.
    + exact Hrng0.
    + lia.
    + exact HSTR3.
    + exact HNA3.
    + apply amem_range_high; [lia | | lia]. lia.
    + unfold snp_out. rewrite Esp3, Esl. unfold seg_spec.SEG_C_SIZE in Hap.
      repeat apply Forall_cons; try apply Forall_nil; unfold zdisjoint;
        cbn [fst snd]; unfold CMD_SNP_K, ESTACK; lia.
  - lia.
  - exact (pb8bn_rom_view _ _ HROD3).
  - exact HFRM. }
cbv beta. intros W4 c4 _ (-> & fx1 & regs4 & mem4 & md4 & Hfx & -> & HJ4 & HP4 & H10b & HBY4 & HK4 & HPR4 & HSM4).
rewrite Esl in HBY4, HK4. rewrite Esb in HBY4.
unfold pf_postm, PF_POSTr. apply (srr_apost_baseF_lift SEGS fx1); [exact Hfx|].
change (mkCfg (@mkst fx1 regs4 (Z_to_bv 64 (BASE + 16620)) mem4 (seg_rom SEGS)) md4)
  with (@cfg_at fx1 SEGS (BASE + PF_B8B_RET_SNPN) regs4 mem4 md4).
(* ---- R3 ---- *)
apply (pb8bn_r3 (fx := fx1) v pos lyc Sc Wc o ln np ds regs4 mem4 md4 _ HJ4).
{ apply (pb8bn_rg_pres rX3 regs4 _ _ HP4 RG3). pb8bn_incl. }
intros rX5 memc5 mdc5 HJ5 K5 RG5.
assert (KK : pb8bn_kept v n (rdW Wc memc) (rdW Wc memc5)).
{ intros a Ha Hw. unfold pb8bn_Wr in Hw. fold ds in Hw. rewrite (K5 a Ha).
  rewrite (HK4 a Ha) by (unfold CMD_SNP_K, ESTACK in *; lia).
  apply (KK3 a Ha). unfold pb8bn_Wr. fold ds. exact Hw. }
(* ---- INV_B8B_JOIN at the FP state the snprintf returned ---- *)
apply (JOIN fx1 v pos lyc Sc Wc rX5 memc5 mdc5 (r_set_segs cf (rc_seg cf ++ [rseg0 (snprintf_s 16 F_s [AS name])]))
  nm o ln d np name n).
split; [|split; [exact HMID|split; [|split; [|split; [|split; [exact HLEN|split]]]]]].
- (* pf_base at fx1 *)
  apply (pb8bn_base_move fx fx1 v pos n lyc Sc Wc rX memc mdc rX5 memc5 mdc5 PF_SC_LINE G KK HBASE HJ5
    (fxrel_frm0 fx fx1 HFRM Hfx)).
  apply (pb8b_rg_sub _ _ _ RG5). intros x Hx. cbn [In] in Hx.
  repeat (destruct Hx as [<- | Hx]; [unfold pb8bn_KR, PF_RL, PF_RM; pb8bn_inS|]). destruct Hx.
- (* pf_st0 *)
  split; [|split; [eapply pb8bn_k_nm; eassumption | exact (pb8bn_cnt_new cf (p_s v) o _ Ho HCNT)]].
  apply (pb8bn_rconf_new (rdW Wc memc) (rdW Wc memc5) (p_c v) cf name HRC HN32 ltac:(lia) Hnz ltac:(lia) Hrng).
  + intros x Hx H1 H2. eapply pb8bn_k_blk; eassumption.
  + intros kk Hkk. unfold seg_spec.RC_N in *.
    rewrite (K5 (p_c v + 11392 + Z.of_nat kk) ltac:(lia)).
    rewrite (HK4 (p_c v + 11392 + Z.of_nat kk) ltac:(lia)) by (unfold CMD_SNP_K, ESTACK; lia).
    rewrite (K3 (p_c v + 11392 + Z.of_nat kk) ltac:(lia)).
    rewrite (HK2 (p_c v + 11392 + Z.of_nat kk) ltac:(lia)) by (unfold ESTACK; lia).
    exact (CN1 kk Hkk).
  + intros i Hi. fold n. fold ds. unfold seg_spec.RC_N in *.
    rewrite (K5 (ds + i) ltac:(lia)).
    destruct (Z_lt_le_dec i (Z.of_nat (length name) + 1)) as [Hlo | Hhi].
    * rewrite (HBY4 i ltac:(lia)). reflexivity.
    * rewrite (HK4 (ds + i) ltac:(lia)) by (unfold CMD_SNP_K, ESTACK; lia).
      rewrite (K3 (ds + i) ltac:(lia)). rewrite (HZ2' i Hi). f_equal. symmetry.
      apply nth_overflow. rewrite length_app. cbn [length]. lia.
- eapply pb8bn_k_buf; eassumption.
- unfold pf_inb, PF_O_BUF. lia.
- cbn [r_set_segs rc_seg]. rewrite length_app. cbn [length]. lia.
- apply (pb8b_rg_sub _ _ _ RG5). intros x Hx. unfold PF_RL, PF_RM in Hx. cbn [In app] in Hx.
  repeat (destruct Hx as [<- | Hx]; [unfold pb8bn_KR, PF_RL, PF_RM; pb8bn_inS|]). destruct Hx.
Qed.
End x2.
End e.
End f.
End d.
