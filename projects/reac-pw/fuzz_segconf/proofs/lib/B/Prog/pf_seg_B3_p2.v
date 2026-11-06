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
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_command/lib/A/Prog/check_round_trip.v, with its module paths and module names changed; 414 of its 496 lines of code are new or changed and 4971 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-pw/fuzz_segconf/lib/B/Prog/pf_seg_B2.v, with its module names and addresses changed; 438 of its 521 lines of code are new or changed and 413 lines of the source are left out. *)
(* reac-pw/fuzz_segconf, image B (fuzz_segconf.asan-ubsan, pin c3796c0b38f3): segment B3 of reac_segconf_parse_file's
   walk, its second piece: MID1 (0x880d0) -> the memset at 0x88130 -> MID2 (0x88134). The B3 segment lane of the image-B G3 walk owner,
   2026-10-30. ADAPTED from the image-A G3 walk owner's image-A segment walk lib/A/Prog/pf_a2.v (commit 3f59c8d75ed4:
   seed, run, region read-back, call step), re-derived on image B's code:
     0x880d0 srli a0,s6,3; add a3,a0,s4; lb a0,0(a3); 0x880dc beqz a0 -> 0x880e4   inline check B#1 (load4 of c->gen;
             slow path 0x891cc .. 0x891e0 not reached: the granule of c + 0x40e0 is addressable, reader_pre's
             sa_addr c SEG_C_SIZE, the token run's shadow entry on atom 22 = s6)
     0x880e4 lw a0,0(s6); lui s2,0x3; addiw a1,s2,-896; ld a2,200(s1); add s3,a2,a1; addi a0,a0,1; sw a0,0(s6)
             c->gen++ (s3 = &c->n = c + 0x2c80)
     0x88100 ld a2,152(s1); 0x88104 bnez s11 -> 0x8810c (t <> 0, reader_pre; the text-NULL return 0x89144 is dead)
     0x8810c sd a3,24(s1); sd s7,72(s1); sd s6,32(s1); a0 = F + 32; sb zero,4(s5); sb zero,5(s5) (cur_name in
             scope); li a2,16; sd a0,64(s1); li a1,0
     0x88130 jal __asan_memset (checked_memset; the listing's pa_sigma SS___asan_memset; return 0x88134)
   Runs: a token run 0x880d0 .. 0x880e4 (the check; every region read-only), then the slots, c->gen and cur_name's
   two shadow cells made writable (PaLibF ast_ok_pi_set_region), a plain run to the call. The call is PaCall's
   aj_intrin_atS (OSet) with pf_pieces.v's hypothesis aintrin_realizes OSet at the memset entry. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YN3v YI00 YI04 YI09.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0s.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YK04 YA0i.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YG00 YG0a YG01.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require seg_spec pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import pf_pieces_spec pfA_facts.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal
SegSyms SegList SegAddr SegPa SegObj SegGlob.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPaLib PaDenot PaLibG PaLibF PaLibH PaCall
PaCallRun PaSB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import SegPgBase SegABase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import refuse_c reac_segconf_parse_file_c SegInstB.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_pieces.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtDefs.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require Import RtPFPf RtPFShared RtPFSx RtPFCmd RtFormat.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import PaArt PaFx.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import pf_seg_B3_f pf_seg_B3_t pf_seg_B3_k pf_seg_B3_p1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require Import YO0a YO0c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope bv_scope.
Open Scope Z_scope.

(* ---------- byte and word facts ---------- *)
Lemma pb3_le_byte_range : forall v n k, 0 <= le_byte v n k < 256.
Proof. intros v n k. unfold le_byte. apply Z.mod_pos_bound. lia. Qed.
Lemma pb3_val_mem_of_sa_val : forall segs H (m : word -> option byte) a (n : nat) v,
  sa_val (aview segs H m) a n v -> val_mem segs (mrestrict H m) a n v.
Proof.
intros segs H m a n v Hv k Hk. specialize (Hv k Hk). unfold aview in Hv.
destruct (mbyte segs (mrestrict H m) (a + Z.of_nat k)) as [b|] eqn:Eb; cbn in Hv; [|discriminate].
injection Hv as Hv. f_equal. rewrite <- (Z_to_bv_bv_unsigned 8 b), Hv. reflexivity.
Qed.
Lemma pb3_sa_val_of_val_mem : forall segs H (m : word -> option byte) a (n : nat) v,
  val_mem segs (mrestrict H m) a n v -> sa_val (aview segs H m) a n v.
Proof.
intros segs H m a n v Hv k Hk. specialize (Hv k Hk). unfold aview. rewrite Hv. cbn [option_map]. f_equal.
rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
change (le_byte v n k mod 256 = le_byte v n k). apply Z.mod_small. apply pb3_le_byte_range.
Qed.
(* lw / addi 1 / sw of a counter g <= 2 ^ 32 - 2: the stored four bytes hold g + 1 *)
Lemma pb3_gen_inc : forall E n g, ew E n = Z_to_bv 64 g -> 0 <= g <= 2 ^ 32 - 2 ->
  bv_unsigned (sv_denot E (SAlu ALU_ADD (SExt true 32 (SOff n 0)) (SLit 1))) mod 2 ^ (8 * Z.of_N 4) = g + 1.
Proof.
intros E n g Hn Hg. change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). cbn [sv_denot]. rewrite Hn.
rewrite (unsigned_lit_small g) by lia. rewrite Z.add_0_r.
rewrite alu64_add, sext64_32_unsigned, bv_extract_unsigned, Z.shiftr_0_r. rewrite (unsigned_lit_small g) by lia.
unfold bv_wrap. change (bv_modulus (Z.to_N 32)) with (2 ^ 32). change (bv_modulus 32) with (2 ^ 32).
rewrite (Z.mod_small g (2 ^ 32)) by lia. rewrite (unsigned_lit_small 1) by lia.
unfold sx32, add64. rewrite (Z.mod_small g (2 ^ 32)) by lia.
destruct (Z.ltb_spec g (2 ^ 31)).
- rewrite (Z.mod_small (g + 1) (2 ^ 64)) by lia. apply Z.mod_small. lia.
- rewrite (Z.mod_small (g + 2 ^ 64 - 2 ^ 32 + 1) (2 ^ 64)) by lia.
  replace (g + 2 ^ 64 - 2 ^ 32 + 1) with ((g + 1) + (2 ^ 32 - 1) * 2 ^ 32) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
(* the shadow address (s6 >> 3) + s4 of c->gen *)
Lemma pb3_den_shx : forall E x, ew E 22 = Z_to_bv 64 x -> ew E 20 = Z_to_bv 64 SHADOW_OFF -> 0 <= x < 2 ^ 47 ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 22 0) (SLit 3)) (SOff 20 0)) = Z_to_bv 64 (shadow_addr x).
Proof.
intros E x E22 E20 Hx.
change (Z_to_bv 64 (shadow_addr x)) with (sv_denot E (SLit (shadow_addr x))).
assert (Hs : 0 <= shadow_addr x < 2 ^ 64)
  by (unfold shadow_addr, SHADOW_OFF; pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia));
      pose proof (Z.div_le_upper_bound x 8 (2 ^ 47) ltac:(lia) ltac:(lia)); lia).
apply U_inj. rewrite U_SAlu, U_srl3. rewrite (U_atom E 22 x E22) by lia.
rewrite (U_atom E 20 SHADOW_OFF E20) by (unfold SHADOW_OFF; lia). rewrite (U_lit E _ Hs).
cbn [zalu_raw]. unfold shadow_addr. rewrite Z.add_comm. apply zcanon_id. unfold M64. unfold shadow_addr in Hs. lia.
Qed.

(* ---------- reading a region the run wrote (pf_a2.v) ---------- *)
Definition pb3_cell_ok (cs : list YP09.chunk) (od v : Z) : bool :=
  existsb (fun c => match YP09.c_val c with
    | CVal w (SLit z) => (YP09.c_off c =? od) && (N.eqb w 1) && (bv_unsigned (byte_of_word (Z_to_bv 64 z) 0) =? v)
    | _ => false end) cs.
Lemma pb3_cell_of_region : forall {rc : YM05.RunCeil} {SK : YI16.sink_head} segs E H m n b lo hi wlo whi cs od v,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) ->
  bv_unsigned (ew E n) = b -> pb3_cell_ok cs od v = true -> aview segs H m (b + od) = Some v.
Proof.
intros rc SK segs E H m n b lo hi wlo whi cs od v HR Hb Hc.
apply existsb_exists in Hc as (c & Hin & Hc).
destruct c as [o [w e | | | ]]; cbn [YP09.c_val YP09.c_off] in Hc; try discriminate.
destruct e; try discriminate.
apply andb_prop in Hc as [Hc Hv]. apply andb_prop in Hc as [Ho Hw].
apply Z.eqb_eq in Ho. apply N.eqb_eq in Hw. apply Z.eqb_eq in Hv. subst o w.
unfold region_ok in HR. cbv zeta in HR. cbn [YP09.r_base YP09.r_chunks base_val] in HR.
destruct HR as (_ & _ & _ & Hcs).
pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck.
destruct (Hck 0 ltac:(cbn; lia)) as (bb & Hb1 & Hb2). cbn [cbyte YP09.c_val YP09.c_off sv_denot] in Hb1, Hb2.
injection Hb1 as <-. rewrite Hb, Z.add_0_r in Hb2.
unfold aview. rewrite Hb2. cbn [option_map]. rewrite Hv. reflexivity.
Qed.
Lemma pb3_word_of_region : forall {rc : YM05.RunCeil} {SK : YI16.sink_head} segs E H m n b lo hi wlo whi cs od e v,
  region_ok segs E (mrestrict H m) (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 8 e)) cs -> sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  rdword (aview segs H m) (b + od) = Some v.
Proof.
intros rc SK segs E H m n b lo hi wlo whi cs od e v HR Hb Hin He Hv.
pose proof (field_of_region_any (segs := segs) E (mrestrict H m) n b cs lo hi wlo whi od 8 e HR Hb Hin
  ltac:(cbn; lia)) as HV.
rewrite He, unsigned_lit_small in HV by lia. change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64) in HV.
rewrite Z.mod_small in HV by lia. change (N.to_nat 8) with 8%nat in HV.
apply rdword_of_val_mem; [exact HV | exact Hv].
Qed.

Ltac pb3_rewin HS i wlo whi wtac :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth i (ss_mem ssx) got_regionP) in
  let HS3 := fresh "HS3" in
  pose proof (ast_ok_pi_set_region Ex ssx msx i r (set_window r wlo whi) HS ltac:(vm_compute; reflexivity) eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow _ Ex _ r wlo whi (st_ok_pi_region_nth Ex ssx msx i r HS ltac:(vm_compute; reflexivity))
    ltac:(cbn [YP09.r_base base_val ms_mem restrict mkst set_window YP09.r_lo YP09.r_hi YP09.r_chunks]; wtac))) as HS3;
  clear HS; rename HS3 into HS;
  lazymatch type of HS with st_ok_pi _ _ _ ?ss3 _ => let v := eval vm_compute in ss3 in change ss3 with v in HS end
  end.

(* ---------- the seed at MID1 (0x880d0) ---------- *)
(* every register its own atom; atoms 32 = F, 33 = c->gen, 34 = c (Ereg's extras); the regions, read-only for the
   token run: the slots s1 + 0x18 .. 0xd0 (F at 0x98, c at 0xc8), c->gen (atom 22 = s6), cur_name's cells (atom 21 =
   s5 = SH); the facts: s4 = SB exactly, s6 in [4096, 2 ^ 47 - 16] and 8-aligned (the check's shadow entry), t >= 1,
   gen <= 2 ^ 32 - 2 *)
Definition pb3_r2s1 : YP09.region := YP09.mkRegion (Some 9%nat) 0x18 0xd0 0x18 0x18
  [YP09.mkChunk 0x98 (CVal 8 (SOff 32 0)); YP09.mkChunk 0xc8 (CVal 8 (SOff 34 0))].
Definition pb3_r2gen : YP09.region := YP09.mkRegion (Some 22%nat) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 33 0))].
Definition pb3_r2sh : YP09.region := YP09.mkRegion (Some 21%nat) 4 6 4 4 [].
Definition pb3_F2 : facts := mkFacts [(20%nat, mkAF SB SB 0); (22%nat, mkAF 4096 (2 ^ 47 - 16) 3);
  (27%nat, mkAF 1 (2 ^ 64 - 1) 0); (33%nat, mkAF 0 (2 ^ 32 - 2) 0)] [] [].
Definition pb3_ss2 : sstate := mkSS (AF_reac_segconf_parse_file + 0x298) sr_atoms [pb3_r2s1; pb3_r2gen; pb3_r2sh] None pb3_F2.
Definition pb3_SH2 : list shent := [mkSHE 22 0 8].

Ltac pb3_q2 HS EE E32 E34 HEI R :=
  lazymatch goal with |- getr (ms_regs ?ms) (Z_to_bv 5 ?k) = _ =>
    let Rk := fresh "Rk" in prreg HS (Z_to_bv 5 k) Rk; rewrite Rk; clear Rk end;
  first
  [ reflexivity
  | rewrite E32; unfold w64; rewrite unsigned_lit_small by lia; f_equal; unfold PF_O_CN; lia
  | rewrite E34; unfold w64; rewrite unsigned_lit_small by lia; f_equal; unfold seg_spec.RC_N; lia
  | lazymatch goal with |- ew _ ?n = _ => let z := eval cbv in (Z.of_nat n) in rewrite (EE n (Z_to_bv 5 z) eq_refl) end;
    apply R; solve [unfold PB3_FI; pb3_in] ].
Ltac pb3_getq QR k := apply (pb3_bvr _ _ k); [reflexivity | apply (pb3_rg _ _ _ _ QR); solve [pb3_in]].

Section d. Context {rc : YM05.RunCeil} {SK : YI16.sink_head} {PI : PAImg seg_listing}.
#[local] Notation SEGS := (@pa_segs _ seg_listing PI).
#[local] Notation VAL := (@pa_val _ seg_listing PI).
#[local] Notation BASE := (@pa_val _ seg_listing PI A_TEXT).
#[local] Notation rdW W mem := (aview SEGS (w_H W) mem).
Variable B : asyms.
(* pf_pieces.v's hypothesis for B3's memset *)
Hypothesis AMEMSET : forall fx0 : YK11.FPState, @aintrin_realizes fx0 rc SEGS B OSet (pa_sigma SS___asan_memset).
Let LAWS : AR_laws SEGS B := YG0q.AR_laws_ok SEGS B.

(* the frame facts the later pieces need from FRAME, free of the FP state (pf_fi's sa_frm0 is not among them) *)
Definition pb3_FA (v : pfv) (pos : Z) (lyc : alayout) (Sc : astate) (Wc : world SEGS) (memA : word -> option byte) : Prop :=
  pf_cx B v /\ pb3_G v pos /\ In (5, pos) (frames Sc) /\ frame_addr lyc 5 pos = pf_F v pos /\ lyc = p_ly v /\
  (exists f, Sc = set_fs f (p_S v)) /\ Permutation (ablocks B lyc Sc) (ablocks B (p_ly v) (p_S v)) /\
  pf_obj B v lyc Sc (rdW Wc memA) /\ pf_saved (rdW Wc memA) (pf_sp0 v) (p_regs v) /\
  rdword (rdW Wc memA) (pf_F v pos + fs_frame_bytes 5 - 8) = Some (pf_FL v pos) /\ pf_tf v pos /\
  frames Sc = (5, pos) :: frames (p_S v).
Lemma pb3_FA_of_frame : forall {fx : YK11.FPState} v pos lyc Sc Wc rX memA mdc,
  INV_FRAME B v pos lyc Sc Wc rX memA mdc -> pb3_FA v pos lyc Sc Wc memA.
Proof.
intros fx v pos lyc Sc Wc rX memA mdc HI.
pose proof HI as (HCX & HFI & HOBJ & _).
destruct (pb3_geo B v pos lyc Sc Wc rX memA mdc HCX HFI (proj1 (proj2 (proj2 (proj2 (proj2 HOBJ))))))
  as (G & Hin & EF & Hfrs & HAR & Hly & _).
pose proof HFI as (_ & _ & HSc & HPm & HSAV & HFL & _ & HTF & _).
repeat (split; [eassumption|]). exact Hfrs.
Qed.
(* T has no NUL: the label is a C string (sa_ostr at the entry), "reac-pw.conf" is one *)
Lemma pb3_T_nonul : forall v, pf_cx B v -> ~ In 0 (pb3_T (p_lab v)).
Proof.
intros v HCX. destruct HCX as (_ & _ & _ & _ & _ & _ & _ & _ & (fe & (_ & HOS & _)) & _).
unfold pb3_T. destruct (p_lab v) as [l|].
- destruct HOS as (_ & ((_ & Hn) & _)). exact Hn.
- intros H. vm_compute in H. repeat (destruct H as [H | H]; [discriminate H|]). exact H.
Qed.

Section x. Context {fx : YK11.FPState}.
Let RUNTO := paj_run_to B LAWS.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.

Lemma pb3_seed2 : forall (Wc : world SEGS) (rX : bvmap 5 word) memc s1 F g c t SH,
  getr rX (Z_to_bv 5 9) = w64 s1 -> getr rX (Z_to_bv 5 20) = w64 SHADOW_OFF -> getr rX (Z_to_bv 5 21) = w64 SH ->
  getr rX (Z_to_bv 5 22) = w64 (c + seg_spec.RC_GEN) -> getr rX (Z_to_bv 5 27) = w64 t ->
  0 <= s1 -> s1 + 0xd0 <= 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= c < 2 ^ 64 ->
  rdword (rdW Wc memc) (s1 + 0x98) = Some F -> rdword (rdW Wc memc) (s1 + 0xc8) = Some c ->
  sa_val (rdW Wc memc) (c + seg_spec.RC_GEN) 4 g -> 0 <= g <= 2 ^ 32 - 2 ->
  4096 <= c + seg_spec.RC_GEN <= 2 ^ 47 - 16 -> (c + seg_spec.RC_GEN) mod 8 = 0 -> 1 <= t < 2 ^ 64 ->
  0 <= SH -> SH + 6 <= 2 ^ 64 ->
  c + seg_spec.RC_GEN + 4 <= s1 + 0x18 -> SH + 6 <= s1 + 0x18 ->
  (c + seg_spec.RC_GEN + 4 <= SH + 4 \/ SH + 6 <= c + seg_spec.RC_GEN) ->
  st_ok_pi SEGS VAL (Eimg (Ereg rX [w64 F; w64 g; w64 c])) pb3_ss2
    (restrict (w_H Wc) (mkst rX (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x298))) memc (seg_rom SEGS))).
Proof.
intros Wc rX memc s1 F g c t SH R9 R20 R21 R22 R27 Hs0 Hs1 HF0 Hc0 W98 WC8 HGV Hg Hcg Hc8 Ht HSH0 HSH1 D1 D2 D3.
set (E := Eimg (Ereg rX [w64 F; w64 g; w64 c])).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr rX r)
  by (intros n r Hn; subst E; apply ew_Eimg_Ereg_nat; exact Hn).
assert (U9 : bv_unsigned (ew E 9) = s1) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl), R9; unfold w64; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew E 20) = SHADOW_OFF)
  by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl), R20; unfold w64; apply unsigned_lit_small; unfold SHADOW_OFF; lia).
assert (U21 : bv_unsigned (ew E 21) = SH) by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl), R21; unfold w64; apply unsigned_lit_small; lia).
assert (U22 : bv_unsigned (ew E 22) = c + seg_spec.RC_GEN)
  by (rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl), R22; unfold w64; apply unsigned_lit_small; lia).
assert (U27 : bv_unsigned (ew E 27) = t) by (rewrite (EE 27%nat (Z_to_bv 5 27) eq_refl), R27; unfold w64; apply unsigned_lit_small; lia).
assert (E32 : ew E 32 = w64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E 33 = w64 g) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E 34 = w64 c) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
assert (U33 : bv_unsigned (ew E 33) = g) by (rewrite E33; unfold w64; apply unsigned_lit_small; lia).
rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
- subst E. apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  + unfold region_ok, pb3_r2s1. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
    * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0x98 8 (SOff 32 0) F).
      -- rewrite pb3_den_atom0, E32. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- cbn. lia.
      -- change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact W98.
    * apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) s1 0xc8 8 (SOff 34 0) c).
      -- rewrite pb3_den_atom0, E34. reflexivity.
      -- change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
      -- cbn. lia.
      -- change (N.to_nat 8) with 8%nat. apply val_mem_of_rdword. exact WC8.
  + unfold region_ok, pb3_r2gen. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U22. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
    apply Forall_cons; [|apply Forall_nil].
    apply (chunk_ok_val SEGS E (mrestrict (w_H Wc) memc) (c + seg_spec.RC_GEN) 0 4 (SOff 33 0) g).
    * rewrite pb3_den_atom0, E33. reflexivity.
    * change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32). lia.
    * cbn. lia.
    * change (N.to_nat 4) with 4%nat. rewrite Z.add_0_r. apply pb3_val_mem_of_sa_val. exact HGV.
  + unfold region_ok, pb3_r2sh. cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U21. split; [lia|]. split; [lia|]. split; [intros o Ho; lia | constructor].
- apply pairwise_disjoint_of_extents. unfold extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val pb3_r2s1 pb3_r2gen pb3_r2sh]. rewrite U9, U22, U21.
  cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
- split; [|split; exact I].
  cbn [f_atoms pb3_F2 atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
  rewrite U20, U22, U27, U33. unfold SB, SHADOW_OFF. change (2 ^ 3) with 8. rewrite Z.pow_0_r, Z.mod_1_r.
  repeat split; try lia.
Qed.

(* ---------- the piece: MID1 (0x880d0) -> memset (0x88130) -> MID2 (0x88134) ---------- *)
Lemma pb3_s2 : forall v pos lyc Sc Wc memA rX memc mdc (Q : world SEGS -> config -> Prop),
  pb3_FA v pos lyc Sc Wc memA -> pb3_MID1 B v pos lyc Sc Wc memA rX memc mdc ->
  (forall rX2 memc2 mdc2, pb3_MID2 B v pos lyc Sc Wc memA rX2 memc2 mdc2 ->
     SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x2fc)) rX2 memc2 mdc2) Q) ->
  SRr SEGS Wc (cfg_at SEGS (BASE + (AF_reac_segconf_parse_file + 0x298)) rX memc mdc) Q.
Proof.
intros v pos lyc Sc Wc memA rX memc mdc Q HFA HM Kc.
destruct HFA as (HCX & G & Hin & EF & Hly & HSc & HPm & HOBJA & HSAV & HFL & HTF & Hfrs).
destruct HM as (HJ & K1 & HRC1 & HSL1 & HFSH1 & HRG1).
pose proof HJ as (HAR & _).
pose proof G as (S1 & S2 & S3 & S4 & S5 & F1 & F2 & F3 & F4 & F5 & C1 & C2 & C3 & C4 & C5 & C6).
pose proof asan_consts as (A1 & _).
pose proof STK_values as (_ & _ & _ & ESTK & _). rewrite ESTK in S1.
destruct (pb3_SHb v pos G) as (ESH & SH1 & SH2 & EF8 & F8).
pose proof HCX as (_ & _ & _ & Hc64 & _ & Ht64 & _ & _ & (fe & ((_ & _ & _ & _ & _ & Hg1 & _ & _ & Ht0 & _ & _ & _ & _ & HTD & _) & _)) & _).
assert (HOBJ1 : pf_obj B v lyc Sc (rdW Wc memc))
  by exact (pb3_keep_obj B v pos lyc Sc Wc memc mdc (rdW Wc memA) (rdW Wc memc) G HAR Hin EF HTD K1 HOBJA).
pose proof HOBJ1 as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & O8 & O9).
pose proof O4 as (_ & Hc63 & Hcam & HcRA & HcHV).
pose proof O5 as (bc & mc & Hbc & Hbc1 & Hbc2).
destruct (al_blocks _ _ LAWS lyc Sc Wc memc mdc bc mc HAR Hbc) as (_ & _ & _ & _ & _ & _ & Hmc).
pose proof (req_size_pos mc ltac:(lia)) as [_ Hrq].
destruct (b3f_rconf_gen_val (rdW Wc memc) (p_c v) _ HRC1) as (Hg0 & HGV).
cbn [pb3_rc1 rc_gen] in Hg0, HGV.
assert (R : forall r x, In (r, x) (PB3_FI B v ++ [(21, pf_SH v pos); (22, p_c v + seg_spec.RC_GEN);
    (23, p_c v + seg_spec.RC_READING); (27, p_t v)]) -> getr rX (Z_to_bv 5 r) = w64 x)
  by (intros r x Hr; exact (pb3_rg rX _ r x HRG1 Hr)).
assert (WF : rdword (rdW Wc memc) (pf_s1 v + 0x98) = Some (pf_F v pos)) by (apply (pb3_sl_get _ _ _ _ _ HSL1); pb3_in).
assert (WC : rdword (rdW Wc memc) (pf_s1 v + 0xc8) = Some (p_c v)) by (apply (pb3_sl_get _ _ _ _ _ HSL1); pb3_in).
pose proof (pb3_seed2 Wc rX memc (pf_s1 v) (pf_F v pos) (rc_gen (p_rcs v)) (p_c v) (p_t v) (pf_SH v pos)
  (R 9 _ ltac:(unfold PB3_FI; pb3_in)) (R 20 _ ltac:(unfold PB3_FI; pb3_in)) (R 21 _ ltac:(unfold PB3_FI; pb3_in))
  (R 22 _ ltac:(unfold PB3_FI; pb3_in)) (R 27 _ ltac:(unfold PB3_FI; pb3_in))
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) WF WC HGV ltac:(lia)
  ltac:(unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia)
  ltac:(unfold seg_spec.RC_GEN; clear -C5;
        apply Z.mod_divide in C5; [destruct C5 as [q Hq]; rewrite Hq; replace (q * 16 + 16608) with ((2 * q + 2076) * 8) by lia; apply Z_mod_mult | lia])
  ltac:(lia) ltac:(unfold kLowMemEnd in *; lia) ltac:(unfold kHighShadowEnd in *; lia)
  ltac:(unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia) ltac:(unfold kHighShadowEnd in *; lia)
  ltac:(unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *; lia))
  as HS.
set (E0 := Eimg (Ereg rX [w64 (pf_F v pos); w64 (rc_gen (p_rcs v)); w64 (p_c v)])) in HS.
assert (HEI : img_env VAL A_LIM E0) by (unfold E0; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E0 n = getr rX r)
  by (intros n r Hn; unfold E0; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E32 : ew E0 32 = w64 (pf_F v pos)) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 0)).
assert (E33 : ew E0 33 = w64 (rc_gen (p_rcs v))) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 1)).
assert (E34 : ew E0 34 = w64 (p_c v)) by (unfold E0; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra rX _ 2)).
clearbody E0.
assert (E9 : ew E0 9 = w64 (pf_s1 v)) by (rewrite (EE 9%nat (Z_to_bv 5 9) eq_refl); apply R; unfold PB3_FI; pb3_in).
assert (E20 : ew E0 20 = w64 SHADOW_OFF) by (rewrite (EE 20%nat (Z_to_bv 5 20) eq_refl); apply R; unfold PB3_FI; pb3_in).
assert (E21 : ew E0 21 = w64 (pf_SH v pos)) by (rewrite (EE 21%nat (Z_to_bv 5 21) eq_refl); apply R; unfold PB3_FI; pb3_in).
assert (E22 : ew E0 22 = w64 (p_c v + seg_spec.RC_GEN)) by (rewrite (EE 22%nat (Z_to_bv 5 22) eq_refl); apply R; unfold PB3_FI; pb3_in).
assert (E23 : ew E0 23 = w64 (p_c v + seg_spec.RC_READING)) by (rewrite (EE 23%nat (Z_to_bv 5 23) eq_refl); apply R; unfold PB3_FI; pb3_in).
assert (U9 : bv_unsigned (ew E0 9) = pf_s1 v) by (rewrite E9; unfold w64; apply unsigned_lit_small; lia).
assert (U21 : bv_unsigned (ew E0 21) = pf_SH v pos) by (rewrite E21; unfold w64; apply unsigned_lit_small; unfold kLowMemEnd, kHighShadowEnd in *; lia).
assert (U22 : bv_unsigned (ew E0 22) = p_c v + seg_spec.RC_GEN)
  by (rewrite E22; unfold w64; apply unsigned_lit_small; unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia).
assert (SHOK : sh_ok SEGS (SOff 20 0) pb3_SH2 E0 (mrestrict (w_H Wc) memc)).
{ unfold sh_ok, pb3_SH2. apply Forall_cons; [|apply Forall_nil].
  apply (shent_ok_of_range SEGS (w_H Wc) memc E0 (SOff 20 0) 22 (p_c v + seg_spec.RC_GEN) 8 (p_c v + seg_spec.RC_GEN) 0 8).
  - apply (range_addressable_sub _ _ _ _ _ _ HcRA); unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE; lia.
  - apply U_atom; [exact E20 | unfold SHADOW_OFF; lia].
  - apply U_atom; [exact E22 | unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia].
  - lia.
  - lia.
  - intros x Hx. cbn in Hx.
    unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE, in_app, kLowShadowBeg, kHighMemBeg, SHADOW_OFF in *. lia. }
unfold cfg_at. change (w64 (BASE + (AF_reac_segconf_parse_file + 0x298)))
  with (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x298))).
(* the check B#1, 0x880d0 .. 0x880e0 *)
paj_run_to_tok RUNTO HS HJ SHOK Bspan (AF_reac_segconf_parse_file + 0x2ac).
{ pb3_ro_awr. }
pb3_clear_md.
assert (KMa : forall a, 0 <= a < 2 ^ 64 -> rdW Wc (ms_mem ms) a = rdW Wc memc a).
{ intros a Ha. apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) memc (ms_mem ms) (fun _ => False) HFr); [|exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; lia |]).
  destruct Hin'. }
assert (MGa : forall a, rdW Wc memc a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) memc (ms_mem ms) a HG Hv)).
clear HF HFr HG.
pose proof HJ as (HARa & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpresa & _).
destruct (al_blocks _ _ LAWS lyc Sc Wc (ms_mem ms) mdv bc mc HARa Hbc) as (_ & _ & _ & _ & Hbpres & _).
destruct (al_frames _ _ LAWS lyc Sc Wc (ms_mem ms) mdv 5 pos HARa Hin) as (_ & _ & _ & Hshp).
rewrite EF in Hshp. change (fs_frame_bytes 5 / 8) with 256 in Hshp. change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hshp.
(* the slots, c->gen and cur_name's two cells become writable *)
pb3_rewin HS 0%nat 0x18 0x50 ltac:(intros o Ho; apply (apresent_writable SEGS); rewrite U9; apply Hpresa; rewrite ESTK; lia).
pb3_rewin HS 1%nat 0 4 ltac:(intros o Ho; apply (apresent_writable SEGS); rewrite U22; apply Hbpres;
  unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia).
pb3_rewin HS 2%nat 4 6 ltac:(intros o Ho; apply (apresent_writable SEGS); rewrite U21; apply Hshp; lia).
rename ms into mtok. rename mdv into mdtok.
(* 0x880e4 .. 0x8812c, to the memset call *)
paj_run_shc RUNP RUNC HS HJ.
{ lazymatch goal with |- awr_ok ?sg ?bb ?Ex ?rs ?stk ?spx ?fp ?b0 ?bc0 ?fr0 ?lyx ?own =>
    let rs' := eval vm_compute in rs in change (awr_ok sg bb Ex rs' stk spx fp b0 bc0 fr0 lyx own) end.
  eapply (awr_ok_cons_stack_off SEGS B _ _ _ _ _ _ _ _ _ _ _ 9%nat (pf_s1 v - pf_sp0 v));
    [reflexivity | rewrite U9; lia | cbn [YP09.r_wlo]; rewrite ESTK; lia | cbn [YP09.r_whi]; lia |].
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 22%nat (p_c v + seg_spec.RC_GEN)); [reflexivity | exact U22 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; left. split.
    - exists (p_c v + seg_spec.RC_READING, p_c v + seg_spec.RC_GEN + 4).
      split; [unfold seg_spec.RC_PARSE_W; right; right; left; reflexivity|].
      cbn [fst snd]. unfold seg_spec.RC_READING, seg_spec.RC_GEN in *. lia.
    - exists bc, mc. split; [exact Hbc|]. unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. lia. }
  eapply (YCbq.awr_ok_cons_gen SEGS B _ _ _ _ _ _ _ _ _ _ _ 21%nat (pf_SH v pos)); [reflexivity | exact U21 | |].
  { intros a Ha. cbn [YP09.r_wlo YP09.r_whi] in Ha. right; right; right; left. exists 5, pos.
    split; [left; reflexivity|]. right. unfold in_zr. cbn [fst snd]. rewrite EF.
    change (fs_frame_bytes 5 / 8) with 256. change (shadow_addr (pf_F v pos)) with (pf_SH v pos). lia. }
  apply awr_ok_nil. }
pb3_clear_md.
(* what the run kept and what it wrote *)
assert (KMt : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v + 0x18 <= a < pf_s1 v + 0x50) ->
    ~ (p_c v + seg_spec.RC_GEN <= a < p_c v + seg_spec.RC_GEN + 4) -> ~ (pf_SH v pos + 4 <= a < pf_SH v pos + 6) ->
    rdW Wc (ms_mem ms) a = rdW Wc (ms_mem mtok) a).
{ intros a Ha N1 N2 N3.
  apply (kept_of_frame (segs := SEGS) E0 _ (w_H Wc) (ms_mem mtok) (ms_mem ms)
    (fun a => (pf_s1 v + 0x18 <= a < pf_s1 v + 0x50) \/ (p_c v + seg_spec.RC_GEN <= a < p_c v + seg_spec.RC_GEN + 4) \/
              (pf_SH v pos + 4 <= a < pf_SH v pos + 6)) HFr); [| exact Ha | tauto].
  intros b wlo whi a' Hin' Hrr. vm_compute in Hin'.
  repeat (destruct Hin' as [Hq | Hin']; [injection Hq as <- <- <-; cbn [base_val] in Hrr; rewrite ?U9, ?U22, ?U21 in Hrr; lia |]).
  destruct Hin'. }
assert (MGt : forall a, rdW Wc (ms_mem mtok) a <> None -> rdW Wc (ms_mem ms) a <> None)
  by (intros a Hv; exact (aview_keeps_vis SEGS (w_H Wc) (ms_mem mtok) (ms_mem ms) a HG Hv)).
lazymatch type of HS with st_ok _ ?Ex ?ssx (restrict _ ?msx) =>
  let r0 := eval vm_compute in (nth 0 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 0 r0 HS ltac:(vm_compute; reflexivity)) as HR0;
  let r1 := eval vm_compute in (nth 1 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 1 r1 HS ltac:(vm_compute; reflexivity)) as HR1;
  let r2 := eval vm_compute in (nth 2 (ss_mem ssx) got_regionP) in
  pose proof (st_ok_region_nth Ex ssx (restrict (w_H Wc) msx) 2 r2 HS ltac:(vm_compute; reflexivity)) as HR2 end.
cbn [ms_mem restrict] in HR0, HR1, HR2.
assert (W18 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0x18) = Some (shadow_addr (p_c v + seg_spec.RC_GEN))).
{ eapply (pb3_word_of_region SEGS E0 (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 0x18 _ _ HR0 U9); [pb3_in | |].
  - apply pb3_den_shx; [exact E22 | exact E20 | unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *; lia].
  - unfold shadow_addr, SHADOW_OFF, seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *.
    pose proof (Z.div_pos (p_c v + 16608) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (p_c v + 16608) 8 (2 ^ 47) ltac:(lia) ltac:(lia)). lia. }
assert (W20 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0x20) = Some (p_c v + seg_spec.RC_GEN)).
{ eapply (pb3_word_of_region SEGS E0 (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 0x20 (SOff 22 0) _ HR0 U9); [pb3_in | |].
  - rewrite pb3_den_atom0. exact E22.
  - unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE in *. lia. }
assert (W40 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0x40) = Some (pf_F v pos + PF_O_CN)).
{ eapply (pb3_word_of_region SEGS E0 (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 0x40 (SOff 32 32) _ HR0 U9); [pb3_in | |].
  - apply pb3_den_off; [exact E32 | lia].
  - unfold PF_O_CN. lia. }
assert (W48 : rdword (rdW Wc (ms_mem ms)) (pf_s1 v + 0x48) = Some (p_c v + seg_spec.RC_READING)).
{ eapply (pb3_word_of_region SEGS E0 (w_H Wc) (ms_mem ms) 9 (pf_s1 v) _ _ _ _ _ 0x48 (SOff 23 0) _ HR0 U9); [pb3_in | |].
  - rewrite pb3_den_atom0. exact E23.
  - unfold seg_spec.RC_READING, seg_spec.SEG_C_SIZE in *. lia. }
assert (VG : sa_val (rdW Wc (ms_mem ms)) (p_c v + seg_spec.RC_GEN) 4 (rc_gen (p_rcs v) + 1)).
{ apply pb3_sa_val_of_val_mem.
  pose proof (field_of_region_any (segs := SEGS) E0 (mrestrict (w_H Wc) (ms_mem ms)) 22 (p_c v + seg_spec.RC_GEN) _ _ _ _ _
    0 4 _ HR1 U22 ltac:(pb3_in) ltac:(cbn; lia)) as HV.
  rewrite (pb3_gen_inc E0 33 (rc_gen (p_rcs v)) E33 ltac:(lia)), Z.add_0_r in HV. exact HV. }
assert (CL : forall i, 4 <= i < 6 -> rdW Wc (ms_mem ms) (pf_SH v pos + i) = Some 0).
{ intros i Hi. apply (pb3_cell_of_region SEGS E0 (w_H Wc) (ms_mem ms) 21 _ _ _ _ _ _ i _ HR2 U21). revert i Hi.
  apply (pb3_zrange (fun i => pb3_cell_ok _ i 0) 4 2). vm_compute. reflexivity. }
(* the registers at the call *)
assert (QR : pf_rg (ms_regs ms) ([(10, pf_F v pos + PF_O_CN); (11, 0); (12, 16)] ++ PB3_FI B v ++
  [(21, pf_SH v pos); (19, p_c v + seg_spec.RC_N); (18, 0x3000); (27, p_t v)])).
{ unfold pf_rg, PB3_FI. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
    pb3_q2 HS EE E32 E34 HEI R. }
assert (Q1 : getr (ms_regs ms) 1 = Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x2fc)))
  by (apply (pb3_bvr _ _ 1); [reflexivity | prreg HS (Z_to_bv 5 1) R1; rewrite R1; reflexivity]).
assert (Q10 : getr (ms_regs ms) 10 = w64 (pf_F v pos + PF_O_CN)) by pb3_getq QR 10.
assert (Q11 : getr (ms_regs ms) 11 = w64 0) by pb3_getq QR 11.
assert (Q12 : getr (ms_regs ms) 12 = w64 16) by pb3_getq QR 12.
assert (Q2 : getr (ms_regs ms) 2 = w64 (pf_s1 v)) by pb3_getq QR 2.
assert (Q3 : getr (ms_regs ms) 3 = w64 (as_gp B)) by pb3_getq QR 3.
assert (Q4 : getr (ms_regs ms) 4 = w64 (as_tp B)) by pb3_getq QR 4.
assert (Hsp : spZ (ms_regs ms) = pf_sp0 v + (pf_s1 v - pf_sp0 v))
  by (unfold spZ; rewrite Q2; unfold w64; rewrite unsigned_lit_small by lia; lia).
pose proof HJ as (HARt & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hprest & _).
destruct (al_frames _ _ LAWS lyc Sc Wc (ms_mem ms) mdv 5 pos HARt Hin) as (_ & _ & Hfbt & Hsht).
rewrite EF in Hfbt, Hsht. change (fs_frame_bytes 5 / 8) with 256 in Hsht. change (fs_frame_bytes 5) with 2048 in Hfbt.
change (shadow_addr (pf_F v pos)) with (pf_SH v pos) in Hsht.
pmkst HS.
eapply SRr_bind.
{ apply (aj_intrin_atS SEGS B LAWS pa_segs_low OSet (pa_sigma SS___asan_memset) (AMEMSET fx) Wc (ms_regs ms) (ms_mem ms)
    STK_reac_segconf_parse_file (pf_sp0 v) (seg_spec.RC_PARSE_W (p_c v)) (p_ly v) (p_S v) (p_W v) (p_mem v) (p_md v)
    [(5, pos)] lyc Sc mdv 0 (pf_F v pos + PF_O_CN) 0 16 (pf_s1 v - pf_sp0 v)
    (Z_to_bv 64 (BASE + (AF_reac_segconf_parse_file + 0x2fc))) HJ Q10 Q11 Q12).
  - lia.
  - unfold PF_O_CN. lia.
  - unfold PF_O_CN. lia.
  - exact Hsp.
  - apply pb3_m16; [exact (pb3_m32_16 _ S5) | exact S3].
  - lia.
  - rewrite ESTK. unfold ESTACK. lia.
  - exact Q3.
  - exact Q4.
  - exact Q1.
  - apply ret_ok_codeptr_v; [unfold AF_reac_segconf_parse_file; lia | reflexivity].
  - intros a Ha. split.
    + right; right; right; left. exists 5, pos. split; [left; reflexivity|]. left. unfold in_zr. cbn [fst snd].
      rewrite EF. change (fs_frame_bytes 5) with 2048. unfold PF_O_CN in Ha. lia.
    + unfold ESTACK, PF_O_CN in *. lia.
  - intros a Ha _ [[_ Hi] | Hs]; exfalso.
    + apply (frm_img SEGS B LAWS lyc Sc Wc (ms_mem ms) mdv 5 pos a HARt Hin); [|exact Hi].
      rewrite EF. change (fs_frame_bytes 5) with 2048. unfold PF_O_CN in Ha. lia.
    + unfold PF_O_CN in Ha. lia.
  - unfold amem_range, in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighMemEnd, ASAN_CEIL, PF_O_CN in *. lia.
  - intros x Hx. exists 0. split; [|left; reflexivity]. unfold shadow_of_addr.
    assert (Hq : x / 8 = pf_F v pos / 8 + 4 \/ x / 8 = pf_F v pos / 8 + 5).
    { unfold PF_O_CN in Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. }
    destruct Hq as [Hq | Hq]; rewrite Hq; rewrite Z.add_assoc, <- ESH; apply CL; lia.
  - intros _ s Hs. apply (aview_some_of_apresent SEGS).
    replace s with (pf_SH v pos + (s - pf_SH v pos)) by lia. apply Hsht.
    unfold shadow_addr, PF_O_CN in Hs. rewrite ESH. unfold SHADOW_OFF in *.
    assert (D1 : (pf_F v pos + 32) / 8 = pf_F v pos / 8 + 4)
      by (replace (pf_F v pos + 32) with (pf_F v pos + 4 * 8) by lia; rewrite Z.div_add by lia; reflexivity).
    assert (D2 : (pf_F v pos + 32 + 16 - 1) / 8 = pf_F v pos / 8 + 5)
      by (replace (pf_F v pos + 32 + 16 - 1) with (7 + (pf_F v pos / 8 + 5) * 8) by lia;
          rewrite Z.div_add by lia; change (7 / 8) with 0; lia).
    rewrite D1, D2 in Hs.
    pose proof (Z.mul_div_le (2147450880 + (pf_F v pos / 8 + 4)) 8 ltac:(lia)).
    pose proof (Z.mul_div_le (2147450880 + (pf_F v pos / 8 + 5)) 8 ltac:(lia)).
    pose proof (Z.mod_pos_bound (2147450880 + (pf_F v pos / 8 + 5)) 8 ltac:(lia)).
    pose proof (Z.div_mod (2147450880 + (pf_F v pos / 8 + 5)) 8 ltac:(lia)).
    lia.
  - exact I. }
cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & Hby & Hkp & Hpr & _).
apply Kc.
pose proof HJ2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres2 & _).
(* every byte outside the segment's piece-2 writes is MID1's *)
assert (K2 : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_s1 v + 0x18 <= a < pf_s1 v + 0x50) ->
    ~ (p_c v + seg_spec.RC_GEN <= a < p_c v + seg_spec.RC_GEN + 4) -> ~ (pf_SH v pos + 4 <= a < pf_SH v pos + 6) ->
    ~ (pf_F v pos + PF_O_CN <= a < pf_F v pos + PF_O_CN + 16) -> ~ (pf_s1 v - ESTACK <= a < pf_s1 v) ->
    rdW Wc mem2 a = rdW Wc memc a).
{ intros a Ha N1 N2 N3 N4 N5. rewrite (Hkp a Ha N4) by (intros Hq; apply N5; lia).
  rewrite (KMt a Ha N1 N2 N3). exact (KMa a Ha). }
assert (KMem : forall a, 0 <= a < 2 ^ 64 -> ~ (pf_F v pos + PF_O_CN <= a < pf_F v pos + PF_O_CN + 16) ->
    ~ (pf_s1 v - ESTACK <= a < pf_s1 v) -> rdW Wc mem2 a = rdW Wc (ms_mem ms) a).
{ intros a Ha N4 N5. apply (Hkp a Ha N4). intros Hq; apply N5; lia. }
assert (Hes : ESTACK = 4096) by reflexivity.
split; [exact HJ2|].
split.
{ apply (pb3_kept_trans v pos _ (rdW Wc memc)); [exact K1|]. split.
  - intros a Ha Hn. apply K2; [exact Ha | | | | |]; intros Hq; apply Hn; unfold pb3_Wr; rewrite ?ESTK;
      unfold seg_spec.RC_READING, seg_spec.RC_GEN, PF_O_CN in *; lia.
  - intros a Ha Hv.
    destruct (Z_lt_le_dec a (pf_F v pos + PF_O_CN)) as [L1 | L1];
    [|destruct (Z_lt_le_dec a (pf_F v pos + PF_O_CN + 16)) as [L2 | L2]].
    + destruct (Z_lt_le_dec a (pf_s1 v - ESTACK)) as [L3 | L3]; [|destruct (Z_lt_le_dec a (pf_s1 v)) as [L4 | L4]].
      * rewrite KMem by lia. exact (MGt a (MGa a Hv)).
      * apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite ESTK. lia.
      * rewrite KMem by lia. exact (MGt a (MGa a Hv)).
    + replace a with (pf_F v pos + PF_O_CN + (a - (pf_F v pos + PF_O_CN))) by lia. rewrite Hby by lia. discriminate.
    + destruct (Z_lt_le_dec a (pf_s1 v - ESTACK)) as [L3 | L3]; [|destruct (Z_lt_le_dec a (pf_s1 v)) as [L4 | L4]].
      * rewrite KMem by lia. exact (MGt a (MGa a Hv)).
      * apply (aview_some_of_apresent SEGS). apply Hpres2. rewrite ESTK. lia.
      * rewrite KMem by lia. exact (MGt a (MGa a Hv)). }
split.
{ rewrite (b3f_pf_start_eq (p_rcs v) (p_lab v) (pb3_T (p_lab v)) eq_refl (pb3_T_nonul v HCX)).
  pose proof (b3f_rconf_gen (rdW Wc memc) (rdW Wc mem2) (p_c v) (pb3_rc1 (p_rcs v) (p_lab v)) HRC1) as HG2.
  cbn [pb3_rc1 rc_seg rc_refusal rc_refused rc_overflow rc_reading rc_gen] in HG2. apply HG2.
  - lia.
  - intros k Hk. rewrite KMem; [exact (VG k Hk) | | |]; unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE, ESTACK, PF_O_CN in *; lia.
  - intros a Ha Hn. apply K2; try lia; unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE, ESTACK, PF_O_CN, in_app,
      kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *; lia. }
split.
{ assert (KSo : forall a, pf_s1 v + 0x50 <= a < pf_s1 v + 0xe0 -> rdW Wc mem2 a = rdW Wc memc a).
  { intros a Ha. apply K2; try lia; unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE, ESTACK, PF_O_CN, kLowMemEnd, kHighShadowEnd in *; lia. }
  assert (KSn : forall a, pf_s1 v <= a < pf_s1 v + 0xe0 -> rdW Wc mem2 a = rdW Wc (ms_mem ms) a).
  { intros a Ha. apply KMem; [lia | | ]; unfold ESTACK, PF_O_CN in *; lia. }
  unfold pf_sl. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  first
  [ rewrite (rdword_ext (rdW Wc memc) (rdW Wc mem2)); [apply (pb3_sl_get _ _ _ _ _ HSL1); solve [pb3_in] | intros k Hk; apply KSo; lia]
  | rewrite (rdword_ext (rdW Wc (ms_mem ms)) (rdW Wc mem2)); [solve [assumption] | intros k Hk; apply KSn; lia] ]. }
split.
{ intros i Hi. rewrite pb3_shb_head by exact Hi.
  destruct (Z_lt_le_dec i 4) as [I1 | I1]; [|destruct (Z_lt_le_dec i 6) as [I2 | I2]].
  - replace ((4 <=? i) && (i <? 6))%bool with false by (symmetry; apply andb_false_iff; left; apply Z.leb_gt; lia).
    rewrite K2; [exact (HFSH1 i Hi) | | | | | |]; unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE, ESTACK, PF_O_CN,
      in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *; lia.
  - replace ((4 <=? i) && (i <? 6))%bool with true by (symmetry; apply andb_true_iff; split; [apply Z.leb_le | apply Z.ltb_lt]; lia).
    rewrite KMem; [exact (CL i ltac:(lia)) | | |]; unfold ESTACK, PF_O_CN, in_app, kLowShadowBeg, kHighMemBeg,
      kLowMemEnd, kHighShadowEnd in *; lia.
  - replace ((4 <=? i) && (i <? 6))%bool with false by (symmetry; apply andb_false_iff; right; apply Z.ltb_ge; lia).
    rewrite K2; [exact (HFSH1 i Hi) | | | | | |]; unfold seg_spec.RC_GEN, seg_spec.SEG_C_SIZE, ESTACK, PF_O_CN,
      in_app, kLowShadowBeg, kHighMemBeg, kLowMemEnd, kHighShadowEnd in *; lia. }
split.
{ intros i Hi. rewrite Hby by exact Hi. reflexivity. }
unfold pf_rg, PB3_FI. cbn [app]. repeat apply Forall_cons; [..|apply Forall_nil]; cbn [fst snd];
  rewrite HP2 by (unfold acallee_saved; lia); apply (pb3_rg _ _ _ _ QR); solve [pb3_in].
Qed.

End x.
End d.
