(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEGMENT PRO of the IMAGE-B walk of fuzz_reply's relay_remove
   (fuzz_reply.asan-ubsan 0x841fc .. 0x8426c), against lib/B/W_relay_remove_cx.v's rr_pro_stmt.  Proves no function
   (kind: segment lemma).  The form is lib/A/W_rr_pro.v's (a working branch): its carry lemmas (brp_carry,
   brp_alock_carry and the footprint lemmas they use) are A's text, renamed; the instruction run is B's.
   B's prologue saves six registers into a 48-byte frame and takes NO fake frame (the journal owns nothing).  The
   walk, from B's objdump:
     0x841fc-0x84214  addi sp,-48 and the six saves (s4 0(sp) .. ra 40(sp));
     0x84218          bltz a0 -> 0x842b8: fd < 0 reloads the six registers and returns (rr_post; nothing changed,
                      no lock, no wake; the found clause is vacuous);
     0x8421c-0x84228  s0 = fd; the GOT word of the shadow cell (A_OBJ 0) and the cell (A_OBJ 30): s2 = SHADOW_OFF;
     0x8422c-0x84234  a0 = &g_lock (A_OBJ 3), pthread_mutex_lock (ALOCK, lifted by W_sites.v aj_gx_entry_at): the
                      lock word goes 0 -> 16;
     0x84238-0x84240  s1 = the auipc image of g_nsrc (A_HI 53), a0 = g_nsrc, blez -> 0x843c0 (RRU None; es = []);
     0x84244-0x84268  s3 = 0, s4 = the auipc image of g_src (A_HI 54), a1 = g_src = G0, a2 = 56 |es|, and the
                      one-time UBSan flags a3 = snez G0 = 1 and a4 = (G0 mod 8 = 0) & a3 = 1 (G0 is a live block:
                      16-aligned and >= 4096; W_traps.v trap_w_snez / trap_w_base_ok) -> RRL 0 at 0x8426c.
   No trap edge lies in this segment.  After the lock a fresh state is seated at 0x84238 with g_nsrc and g_src as
   read-only regions (the runs after it write nothing). *)
(* Modified by Theorem Labs, 2026-10: ROUTE (b), STEP 3 (lane RRX, the image-A twin a Theorem Labs lane f4cd818e98d
   lib/A/W_rr_pro.v): PRO over ARx in the room form, IN PLACE (the AR proof is dropped, a Theorem Labs lane 10:34Z).  Section c
   is W_relay_remove_cx.v's generic block; the runs are W_journal_x.v's paj_run_x_x / paj_run_to_x_x (W_kit_x.v
   paj_run_tok_x / paj_run_to_tok_x), the entry journal is ajournal_gx_init_x at RR_STK_x (in place of RR_STK), the
   lock is lifted by W_sites_x.v aj_gx_entry_at_x (in place of W_sites.v aj_gx_entry_at) with ALOCK : alock_realizes_x,
   the laws are AR_laws_x's alx_*, and brp_entry / brp_wt_lo / brp_carry take the head sets.  Image B takes no fake
   frame (image A's seat aj_stack_malloc_pres_at_raw_x has no image-B counterpart), so the state S is never changed:
   the lock keeps S and the head set Hp, so every cut's head set is the entry's Hp and RHELD's two room conjuncts are
   RBASE's (rp_RM RP S (Z.to_nat (tr_cost MT_rk tr) + kr) and cnt_ok_pk RP (rr_pk tr) at the entry's blocks); the
   fd < 0 arm returns rr_post_x (in place of rr_post), whose budget kr is below RBASE's by RMM_of. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep gestures_end_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require relay_remove_b_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_contract W_rep W_journal W_sites W_frame W_wake_c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG YGcallx YC80x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_kit_x W_journal_x W_sites_x W_contract_x W_frame_x W_wake_c_x.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyCnt.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_relay_remove_cx.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_traps.
(* route R (the Section wR below): SRrG, and the R contract texts of drain / gestures_end (a Theorem Labs lane) and of
   relay_remove (a Theorem Labs lane) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR W_contract_xR_relayB.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

(* fd as a signed 64-bit word (A's fd_signed) *)
Lemma brp_fd_signed : forall fd, - 2 ^ 31 <= fd < 2 ^ 31 -> bv_signed (Z_to_bv 64 fd) = fd.
Proof.
intros fd Hfd. assert (HU : bv_unsigned (Z_to_bv 64 fd) = if fd <? 0 then fd + 2 ^ 64 else fd).
{ rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
destruct (Z.ltb_spec fd 0); [symmetry; apply (Z.mod_unique fd (2 ^ 64) (-1)); lia | apply Z.mod_small; lia]. }
destruct (Z.ltb_spec fd 0).
- rewrite bv_signed_hi by lia. lia.
- rewrite bv_signed_small by lia. lia.
Qed.
(* s5 .. s11 by cases *)
Lemma brp_s5s11 : forall (f g : bvmap 5 word),
getr f 21 = getr g 21 -> getr f 22 = getr g 22 -> getr f 23 = getr g 23 -> getr f 24 = getr g 24 ->
getr f 25 = getr g 25 -> getr f 26 = getr g 26 -> getr f 27 = getr g 27 ->
forall r : bv 5, 21 <= bv_unsigned r <= 27 -> getr f r = getr g r.
Proof.
intros f g H21 H22 H23 H24 H25 H26 H27 r Hr.
assert (Hc : bv_unsigned r = 21 \/ bv_unsigned r = 22 \/ bv_unsigned r = 23 \/ bv_unsigned r = 24 \/
  bv_unsigned r = 25 \/ bv_unsigned r = 26 \/ bv_unsigned r = 27) by lia.
destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]]].
- assert (r = 21%bv) as -> by (apply bv_eq; rewrite Hc; reflexivity). exact H21.
- assert (r = 22%bv) as -> by (apply bv_eq; rewrite Hc; reflexivity). exact H22.
- assert (r = 23%bv) as -> by (apply bv_eq; rewrite Hc; reflexivity). exact H23.
- assert (r = 24%bv) as -> by (apply bv_eq; rewrite Hc; reflexivity). exact H24.
- assert (r = 25%bv) as -> by (apply bv_eq; rewrite Hc; reflexivity). exact H25.
- assert (r = 26%bv) as -> by (apply bv_eq; rewrite Hc; reflexivity). exact H26.
- assert (r = 27%bv) as -> by (apply bv_eq; rewrite Hc; reflexivity). exact H27.
Qed.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ---- The walk's local pcs and seats. ---- *)
Definition brp_held : Z := AF_fr_relay_remove + 0x3c.      (* 0x84238, pthread_mutex_lock's return *)
Definition brp_Bx : sv := SOff 32 0.
Definition brp_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the entry: the 48-byte frame, the GOT word of the shadow cell and the cell (atom 32 = SB) *)
Definition brp_regions0 : smem := [ stack_region RR_FRAME; got_regionP; bcell_regionP 32 ].
Definition brp_atoms0 : list (nat * afact) := [ (2%nat, mkAF (2^46) (2^47) 5); (32%nat, mkAF SB SB 0) ].
Definition brp_ss0 : sstate := mkSS A_rr_entry sr_atoms brp_regions0 None (mkFacts brp_atoms0 [] []).
Definition brp_extra : list word := map (Z_to_bv 64) [SB].
(* the seat at 0x84238: g_nsrc (atom 32 = |es|) and g_src (atom 33 = G0) read-only at their objects *)
Definition brp_hregions : smem :=
[ YP09.mkRegion (Some (A_OBJ 4)) 0 4 0 0 [YP09.mkChunk 0 (CVal 4 (SOff 32 0))];
  YP09.mkRegion (Some (A_OBJ 5)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))] ].
Definition brp_ssh : sstate := mkSS brp_held sr_atoms brp_hregions None (mkFacts [] [] []).
Definition brp_hextra (n g : Z) : list word := map (Z_to_bv 64) [n; g].
Definition brp_hBx : sv := SOff 18 0.
(* the registers the walk keeps from the entry up to the lock, and from the lock's return to the cuts *)
Definition BRP_KEPT0 : list (bv 5) := [3; 4; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition BRP_KEPT : list (bv 5) := [1; 2; 3; 4; 8; 18; 21; 22; 23; 24; 25; 26; 27]%bv.
(* the six saved registers, in their frame order s4 0(sp) .. ra 40(sp) (W_relay_remove_cx.v RR_SAVED) *)
Definition brp_saved_atoms : list nat := [20; 19; 18; 9; 8; 1]%nat.

(* after a run whose regions have no write window: the memory is the one it began in (B's W_rr_scan.v rrs_mem) *)
Ltac brp_mem Em :=
lazymatch goal with HF : frame_of ?E ?rs ?m (ms_mem ?x) |- _ =>
  pose proof (frame_of_read_only E rs m (ms_mem x) ltac:(vm_compute; reflexivity) HF) as Em end;
repeat match goal with Hx : frame_of _ _ _ _ |- _ => clear Hx | Hx : mem_grows _ _ |- _ => clear Hx end.
(* the write obligation of a run over read-only regions *)
Ltac brp_awr0 :=
repeat (apply awr_ok_x_cons; [let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; cbn in Ha; lia |]);
apply awr_ok_x_nil.
(* after a writing run: its frame over the unhidden memory as HFr, its growth as HGr; the raw frame dropped *)
Ltac brp_grab :=
lazymatch goal with Hf : frame_of _ _ (mrestrict _ _) (mrestrict _ _) |- _ => rename Hf into HFr_x; rename HFr_x into HFr end;
lazymatch goal with Hg : mem_grows (mrestrict _ _) (mrestrict _ _) |- _ => rename Hg into HGr_x; rename HGr_x into HGr end;
try match goal with Hf : frame_of _ _ ?x _ |- _ => lazymatch x with mrestrict _ _ => fail | _ => clear Hf end end.
(* the regions' write windows (the frame's 48 bytes only) hold no watched byte: WA the byte's range, WB the floor *)
Ltac brp_nowin WA WB :=
split; [revert WA; pose proof asan_consts as (Cx & _); revert Cx; clear; intros; lia |
let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
intros (r & Hin & Hr);
lazymatch type of Hin with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin end;
cbn [In] in Hin;
repeat (destruct Hin as [<- | Hin];
 [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
   repeat match goal with Hu : bv_unsigned (ew _ _) = _ |- _ => progress rewrite Hu in Hr end;
   revert Hr; clear - WA WB; intros Hr; lia | ]);
destruct Hin ].

Section c.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Variable MT : ameter_ops.
(* the room round (W_journal_x.v Record roomp): the allocator's room invariant and the live counts, after MT *)
Variable RP : roomp.
Variable MMAX : Z.
Variable RG : rep_globals.
(* the allocator rules on the _c form (W_journal.v Section hc; a Theorem Labs lane 21:24Z): one table CTX_AFREE for free and
   free(NULL), which enter the same interceptor pc0.  Image B's relay_remove keeps NO frame pointer: at its free
   (0x8435c, ra 0x84360 = entry + 0x164) s0 holds fd, an integer below alloc_ceiling, so chain_pre's chain is cut by
   the register and the trace is the CLOSED singleton [0x84360] (a Theorem Labs lane 21:32Z; K0's B CTX_AFREE row, lib/B/YCk0.v:19).  The
   kit's B rr_spec_x takes it as its LAST premise `In [pc + 356] CTX_AFREE` (W4's b_facts, a Theorem Labs lane 21:5xZ); RCTX
   below carries it to MATCH's free (no ly_top conjunct: the chain is []). *)
Variable CTX_AFREE : list (list Z).
Context {hl : Z}.
(* ---- The Section hypotheses every segment file copies (the names are the contracts'). ---- *)
(* the generic relation's laws and its empty head set (CONVERSION.md (sha256 1015972e02a9; internal record) 1.) *)
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Hypothesis TL : PALib B.
Hypothesis TLF : PALibF B.
(* the frame twins' hypotheses (W_frame_x.v): the image cover IMGC (image B's top, W_wake_x.v's form), a live block's
   size non-negative (BLKN, W_kit_x.v), the owned-low law OWNLOW, the model invariant WFx with its law WFL and the two
   facts the twins read off model_laws / stack_malloc_progressP (SFREE, SMALLOC); ASMP / ASF / FFL are the class-0
   fake frame's laws (image B's relay_remove takes none: wake does, W_wake_x.v) *)
Hypothesis IMGC : forall ly S Hp W mem md, ARx ly S Hp W mem md ->
fst (ly_img ly) <= 0x10000 /\ 0x5fc000 <= fst (ly_img ly) + snd (ly_img ly).
Hypothesis BLKN : forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) -> 0 <= n.
Hypothesis OWNLOW : ARx_owned_low_law SEGS B ARx.
Variable WFx : astate -> Prop.
Hypothesis WFL : ARx_wf_law SEGS ARx WFx.
Hypothesis SFREE : forall s cid pos, WFx s -> In (cid, pos) (frames s) ->
exists l1 l2, frames s = l1 ++ (cid, pos) :: l2 /\ frames (stack_free_state cid pos s) = l1 ++ l2.
Hypothesis SMALLOC : forall s cid, WFx s -> 0 <= cid <= 10 -> count_cid cid (frames s) < fs_frames cid ->
exists pos s', apath (stack_malloc cid s) [] (PFake cid pos, s') /\ (exists f, s' = set_fs f s) /\
frames s' = (cid, pos) :: frames s /\ ~ In (cid, pos) (frames s).
Hypothesis ASMP : astack_malloc_pres_x SEGS B ARx 0.
Hypothesis ASF : astack_free_law_x SEGS B ARx.
Hypothesis FFL : frame_flag_lawP_x SEGS B ARx.
Hypothesis HG : gx_ok SEGS B (G_RR B RG).
(* the register images of g_nsrc / g_src (the abstract placement does not fix them against the objects; PB_fr on
   AsanUbsan discharges both by vm_compute, as the image-A twin's HH59 / HH60) *)
Hypothesis HH53 : VAL (A_HI 53) = rg_nsrc RG + RR_HI_NSRC.
Hypothesis HH54 : VAL (A_HI 54) = rg_src RG + RR_HI_SRC.
(* the relay's and the output's global cells are pairwise apart, and errno with them; the four that neither rg_place
   nor gx_ok places are unowned image bytes (the image-A twin's HRGP / HRGI, verbatim) *)
Hypothesis HRGP : zpairwise_disjoint
[(rg_lock RG, rg_lock RG + 12); (rg_s RG, rg_s RG + 4 * ASRC); (rg_src RG, rg_src RG + 8);
 (rg_nsrc RG, rg_nsrc RG + 4); (rg_capsrc RG, rg_capsrc RG + 4); (rg_send_max RG, rg_send_max RG + 8);
 (rg_nout RG, rg_nout RG + 8); (rg_capout RG, rg_capout RG + 8); (rg_out RG, rg_out RG + 8);
 (rg_client RG, rg_client RG + 4); (rg_client_broken RG, rg_client_broken RG + 1);
 (rg_send_dead RG, rg_send_dead RG + 1); (rg_send_eintr RG, rg_send_eintr RG + 1); (rg_wake RG + 4, rg_wake RG + 8);
 (as_errno B, as_errno B + 4)].
Hypothesis HRGI : forall a,
(rg_capsrc RG <= a < rg_capsrc RG + 4 \/ rg_send_max RG <= a < rg_send_max RG + 8 \/
 rg_client RG <= a < rg_client RG + 4 \/ rg_send_dead RG <= a < rg_send_dead RG + 1) ->
in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B).
(* no read-only image byte is owned by the runtime: rom_view survives the calls (W_journal_x.v ajournal_gx_rom_view_x) *)
Hypothesis HROMO : rom_out SEGS B (G_RR B RG).
Hypothesis MLAW : ameter_laws MT.
(* the meter does not see a change of the fake-frame state alone (KF-COUNT, the image-A twin's MO_FR): sound, since
   the seat's post state is a set_fs (Reusable/YG01.v stack_malloc_post) and the release is stack_free_state, a set_fs;
   image B meets it at wake's return (W_wake_c_x.v wk_post_x's seat fact S' = set_fs f S) *)
Hypothesis MO_FR : forall s f, mo_le MT s (set_fs f s) 0.
(* the runtime entries relay_remove calls, at their SIGMA pcs (image B calls free's interceptor directly, WS_free) *)
Hypothesis ALOCK : alock_realizes_x B ARx (SIGMA WS_pthread_mutex_lock).
Hypothesis AUNLOCK : aunlock_realizes_x B ARx (SIGMA WS_pthread_mutex_unlock).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
Hypothesis AMEMCPY : aintrin_realizes_x SEGS B ARx OCpy (SIGMA WS_asan_memcpy).
Hypothesis AMEMCPYS : amemcpy_same_realizes_x B ARx (SIGMA WS_asan_memcpy).
(* the program functions relay_remove calls: drain, gestures_end (the kit's _x specs) and wake (W_wake_c_x.v) *)
Hypothesis DRAIN : dr_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE : gse_spec_x B PST ARx MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* free (s->buf) at 0x8435c with s->buf = NULL (an entry with cap 0) *)
Hypothesis AFREEN : afree_null_cf_rule_c_x SEGS B PST ARx MT RP CTX_AFREE.
(* B only: wake, tail-called at 0x843e8 (image A inlines it); W_relay_remove.v builds it by W_wake_x.v pb_wake_x *)
Hypothesis WAKE : wk_spec_x B PST ARx RG (BASE + AF_fr_wake).
(* the bytes of " end\0" (.str.4, read-only .rodata), which gse_spec's / ge_spec's premise garr8 (VAL A_lit_end5)
   (bzs END5) needs with rom_view (no zero-shadow fact: the literal's last shadow granule is partial): k3's HEND5L, verbatim (W_drain_cx.v dlit_at form; PB_fr
   by vm_compute) *)
Hypothesis HEND5L : forall k, (k < 5)%nat -> YG0d.in_rom SEGS (VAL A_lit_end5 + Z.of_nat k) /\
  seg_rom SEGS (Z_to_bv 64 (VAL A_lit_end5 + Z.of_nat k)) = nth_error END5 k.
(* The program statics PST hold no byte the walk carries through a journal's image clause, which exempts PST
   (YCbqG.v ajournal_x): no read-only byte (ajournal_gx_rom_view_x) and no byte of the relay's / output's cells or
   errno (rr_gcells, HRGP's list).  At PST := [] both hold trivially (the image-A twin's PSTR / PSTG, verbatim). *)
Hypothesis PSTR : forall a, in_rom SEGS a -> ~ Exists (in_zr a) PST.
Hypothesis PSTG : forall a, Exists (fun r => fst r <= a < snd r) (rr_gcells B RG) -> ~ Exists (in_zr a) PST.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
(* the token runners over W_journal_x.v's generic chain (ajournal_gx_x, the head sets after the states) *)
Let RUN := paj_run_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS (G_RR B RG) HG 0 [].
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- The entry state. ---- *)
Lemma brp_entry : forall W ly S Hp regs mem md ch,
afn_pre_x SEGS B ARx RR_STK_x ly S Hp W regs mem md ch -> spZ regs mod 32 = 0 ->
st_ok_pi SEGS VAL (Eimg (Ereg regs brp_extra)) brp_ss0
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_rr_entryP) mem (seg_rom SEGS)))
/\ sh_ok SEGS brp_Bx [] (Eimg (Ereg regs brp_extra)) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch HPRE H32.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RR_STK_x = 17056) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs brp_extra)). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (EO : forall i, (i < 31)%nat -> ew E (A_OBJ i) = Z_to_bv 64 (VAL (A_OBJ i)))
by (intros i Hi; subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (VBO : forall i, (i < 31)%nat -> base_val E (Some (A_OBJ i)) = VAL (A_OBJ i)).
{ intros i Hi. apply VB; [exact (EO i Hi) | exact (pa_val_range _)]. }
split.
- unfold brp_ss0, A_rr_entryP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold brp_regions0, stack_region, got_regionP, bcell_regionP.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [unfold RR_FRAME; lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. unfold RR_FRAME in Ho. lia.
* rewrite (VBO 0%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite (EO 30%nat ltac:(lia)), Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VBO 30%nat ltac:(lia)). split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 (SOff 32 0) SB);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
+ apply pairwise_disjoint_of_extents. unfold brp_regions0, stack_region, got_regionP, bcell_regionP, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VBO 0%nat ltac:(lia)), (VBO 30%nat ltac:(lia)). cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR. clear.
unfold RR_FRAME, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [brp_atoms0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E32, !unsigned_lit_small by (unfold SB; lia).
change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r.
revert Hslo Hshi H47 Hceil Hal16 H32 C1 C3 WS Hstk0. clear.
unfold SB, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok. constructor.
Qed.

(* the six saved registers, read off the frame's stack region (A's rr_saved_of_region) *)
Lemma brp_saved_of_region : forall E (W : world SEGS) memX regs lo hi wlo whi cs,
region_ok SEGS E (mrestrict (w_H W) memX) (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) ->
(forall i, (i < 6)%nat -> In (YP09.mkChunk (-48 + 8 * Z.of_nat i) (CVal 8 (SOff (nth i brp_saved_atoms 0%nat) 0))) cs) ->
(forall (n : nat) (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r) ->
forall i, (i < 6)%nat ->
val_mem SEGS (arm W memX) (bv_unsigned (ew E 2) - RR_FRAME + 8 * Z.of_nat i) 8
  (bv_unsigned (getr regs (nth i RR_SAVED 0%bv))).
Proof.
intros E W memX regs lo hi wlo whi cs HR Hin EREG i Hi.
assert (Hew : ew E (nth i brp_saved_atoms 0%nat) = getr regs (nth i RR_SAVED 0%bv)).
{ apply EREG; (do 6 (destruct i as [|i]; [first [reflexivity | cbn [nth brp_saved_atoms]; lia] |])); lia. }
replace (bv_unsigned (ew E 2) - RR_FRAME + 8 * Z.of_nat i)
  with (bv_unsigned (ew E 2) + (-48 + 8 * Z.of_nat i)) by (unfold RR_FRAME; lia).
unfold arm.
apply (slot_of_region E _ _ cs lo hi wlo whi _ (SOff (nth i brp_saved_atoms 0%nat) 0) _ HR eq_refl (Hin i Hi)).
- cbn [sv_denot]. rewrite Hew, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
- pose proof (bv_unsigned_in_range 64 (getr regs (nth i RR_SAVED 0%bv))) as R.
  change (bv_modulus 64) with (2 ^ 64) in R. lia.
Qed.

(* ---- What the walk carries (lib/A/W_rr_pro.v's text, renamed).  The walk writes the frame and g_lock's lock word
   only; every byte the entry's representations read is an image byte not owned by the runtime or a byte of a live
   block of the entry (brp_wt), and is kept. ---- *)
Definition brp_wt (ly : alayout) (S : astate) (a : Z) : Prop :=
(in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B)) \/
(exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + req_size n).
Definition brp_lkw (a : Z) : Prop := rg_lock RG + 4 <= a < rg_lock RG + 8.
Lemma brp_wt_blk : forall ly S p n a, In (p, n) (ablocks B ly S) -> p <= a < p + n -> brp_wt ly S a.
Proof.
intros ly S p n a Hin Ha. right. exists p, n. split; [exact Hin|].
destruct (Z_le_gt_dec 0 n) as [Hn | Hn]; [pose proof (req_size_pos n Hn); lia | lia].
Qed.
Lemma brp_wt_lo : forall ly S Hp (W : world SEGS) m md a, ARx ly S Hp W m md -> brp_wt ly S a ->
4096 <= a < alloc_ceiling.
Proof.
intros ly S Hp W m md a HAR [(Hi & _) | (p & n & Hin & Ha)].
- pose proof (pa_img_range a Hi). pose proof asan_consts as (C1 & _). lia.
- destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR Hin) as (_ & H4096 & Hceil & _). lia.
Qed.
(* a watched byte that is not an image byte (a live block's) is none of g_lock's *)
Lemma brp_wt_nlk : forall a, rg_place B RG -> ~ in_img SEGS a -> ~ (rg_lock RG <= a < rg_lock RG + 12).
Proof.
intros a RGP Hni Ha. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
apply Hni. apply (RGIMG a). unfold rg_rng. left. exact Ha.
Qed.
Lemma brp_kv_run : forall E rs (W : world SEGS) mem m1 m2 (P : Z -> Prop),
(forall a, P a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a) ->
frame_of E rs (mrestrict (w_H W) m1) (mrestrict (w_H W) m2) ->
(forall a, P a -> 0 <= a < 2 ^ 64 /\ ~ in_wrange E rs a) ->
forall a, P a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a.
Proof.
intros E rs W mem m1 m2 P K HF Hn a Ha. destruct (Hn a Ha) as [H1 H2].
rewrite (aview_kept_out E rs (w_H W) m1 m2 HF a H1 H2). exact (K a Ha).
Qed.
Lemma brp_pres_grow : forall (H : word -> bool) (m0 m1 m2 : word -> option byte),
(forall a, in_img SEGS a -> apresent H m0 a -> apresent H m1 a) ->
mem_grows (mrestrict H m1) (mrestrict H m2) ->
forall a, in_img SEGS a -> apresent H m0 a -> apresent H m2 a.
Proof.
intros H m0 m1 m2 P Hgr a Hi Ha. exact (apresent_grows _ _ _ _ Hgr (P a Hi Ha)).
Qed.
(* g_lock's twelve bytes are watched (rg_place): kept, they keep alock_at *)
Lemma brp_alock_carry : forall ly S (W : world SEGS) mem m1 (X : Z -> Prop) b,
(forall a, brp_wt ly S a -> ~ X a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a) ->
(forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) m1 a) ->
(forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ X a) ->
rg_place B RG -> alock_at RG W mem b -> alock_at RG W m1 b.
Proof.
intros ly S W mem m1 X b KV PR HX RGP HL. destruct RGP as (_ & _ & _ & _ & _ & _ & RGIMG & _).
apply (alock_at_kept RG W mem W m1 b HL). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hi & Ho & _).
split; [apply KV; [left; split; assumption | exact (HX a Ha)]|].
unfold arm. apply writable_kept. intros Hp. exact (PR a Hi Hp).
Qed.
(* ---- The entry's representations at a later memory m1 of the same world: every watched byte (outside X, a part
   of g_lock's lock word) kept, image presence kept, the live blocks the same. ---- *)
Ltac brp_in := repeat (first [left; reflexivity | right]).
Lemma brp_recs_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
intros rs. induction rs as [|r rs IH]; [reflexivity|].
cbn [map concat length]. rewrite length_app, IH. unfold text_rec.
rewrite length_app, !OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. lia.
Qed.
Lemma brp_kptrs_len : forall ks, length (key_ptrs ks) = (8 * length ks)%nat.
Proof.
intros ks. induction ks as [|k ks IH]; [reflexivity|]. unfold key_ptrs in *. cbn [map concat]. rewrite length_app, IH.
rewrite OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.length_le8. cbn [length]. lia.
Qed.
(* the bytes an entry's predicate reads lie in its blocks, which are live *)
Lemma brp_entry_fp : forall ly S (W : world SEGS) mem e, aentry_ok B ly S W mem e ->
(forall r, In r (aentry_fp e) -> forall a, fst r <= a < snd r ->
  exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + n) /\
(forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
intros ly S W mem e (_ & _ & _ & _ & _ & _ & HU & _ & _ & Hbuf & _ & Hhp & _ & _ & Hks).
split.
- intros r Hr a Ha. unfold aentry_fp in Hr. apply in_app_or in Hr. destruct Hr as [Hr | [<- | Hr]].
  + destruct (Z.eqb_spec (re_cap e) 0) as [Hc0 | Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, length_app in Ha.
    destruct Hbuf as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    exists (re_buf e), (re_cap e). split; [exact Hin | lia].
  + unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map, brp_kptrs_len in Ha.
    destruct Hhp as [(_ & Hk0) | (_ & Hin & Hk1 & _)].
    * rewrite Hk0 in Ha. cbn [length] in Ha. lia.
    * exists (re_hp e), (re_kh e). split; [exact Hin|]. unfold re_nheld in Hk1. lia.
  + apply in_map_iff in Hr as (k & <- & Hk). unfold gfp, bzs in Ha. cbn [fst snd] in Ha.
    rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hks. destruct (Hks k Hk) as (Hin & _).
    exists (key_addr k), (Z.of_nat (length (key_text k)) + 1). split; [exact Hin | lia].
- intros b Hb. unfold aentry_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (re_cap e) 0) as [Hc0 | Hc0]; cbn [In] in Hb; [destruct Hb|].
    destruct Hb as [<- | []]. destruct Hbuf as [(Hc & _) | (_ & Hin & _)]; [lia | exact Hin].
  + apply in_app_or in Hb. destruct Hb as [Hb | Hb].
    * destruct (Z.eqb_spec (re_hp e) 0) as [Hh0 | Hh0]; cbn [In] in Hb; [destruct Hb|].
      destruct Hb as [<- | []]. destruct Hhp as [(Hh & _) | (_ & Hin & _)]; [lia | exact Hin].
    * apply in_map_iff in Hb as (k & <- & Hk). rewrite Forall_forall in Hks. exact (proj1 (Hks k Hk)).
Qed.
(* the same for a list header at LA (bytes of g_s) and the blocks it names *)
Lemma brp_alist_fp : forall ly S (W : world SEGS) mem LA l lines, alist_at B ly S W mem LA l lines ->
(forall r, In r (alist_fp LA l) -> forall a, fst r <= a < snd r ->
  LA <= a < LA + 16 \/ exists p n, In (p, n) (ablocks B ly S) /\ p <= a < p + n) /\
(forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
intros ly S W mem LA l lines (_ & _ & _ & _ & Hn & Hv & _ & _ & Hrecs).
split.
- intros r Hr a Ha. unfold alist_fp in Hr. destruct Hr as [<- | Hr]; [left; cbn [fst snd] in Ha; lia|].
  right. apply in_app_or in Hr. destruct Hr as [Hr | Hr].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0 | Hc0]; cbn [In] in Hr; [destruct Hr|].
    destruct Hr as [<- | []]. unfold gfp, bzs in Ha. cbn [fst snd] in Ha.
    rewrite length_map, length_app, brp_recs_len in Ha.
    destruct Hv as [(Hc & _) | (Hc & Hin & Hj & _)]; [lia|].
    exists (hl_v l), (AREC * hl_cap l). split; [exact Hin|]. unfold hl_n in *. unfold AREC in *. lia.
  + apply in_map_iff in Hr as (q & <- & Hq). unfold gfp, bzs in Ha. cbn [fst snd] in Ha.
    rewrite length_map, length_app in Ha. cbn [length] in Ha.
    rewrite Forall_forall in Hrecs. destruct (Hrecs q Hq) as (Hin & _).
    exists (fst q), (Z.of_nat (length (snd q)) + 1). split; [exact Hin | lia].
- intros b Hb. unfold alist_blks in Hb. apply in_app_or in Hb. destruct Hb as [Hb | Hb].
  + destruct (Z.eqb_spec (hl_cap l) 0) as [Hc0 | Hc0]; cbn [In] in Hb; [destruct Hb|].
    destruct Hb as [<- | []]. destruct Hv as [(Hc & _) | (_ & Hin & _)]; [lia | exact Hin].
  + apply in_map_iff in Hb as (q & <- & Hq). rewrite Forall_forall in Hrecs. exact (proj1 (Hrecs q Hq)).
Qed.
Lemma brp_carry : forall ly S S1 HpA HpB (W : world SEGS) mem md m1 md1 G0 es c O mx cap out h j FD (X : Z -> Prop),
ARx ly S HpA W mem md -> ARx ly S1 HpB W m1 md1 -> ablocks B ly S1 = ablocks B ly S ->
(forall a, brp_wt ly S a -> ~ X a -> aview SEGS (w_H W) m1 a = aview SEGS (w_H W) mem a) ->
(forall a, in_img SEGS a -> apresent (w_H W) mem a -> apresent (w_H W) m1 a) ->
(forall a, X a -> brp_lkw a) ->
rg_place B RG ->
arelay_at B RG ly S W mem G0 es ->
aout_at B RG ly S W mem c O mx (Z.of_nat (length O)) cap out ->
awake_at RG W mem ->
(forall i, (i < length es)%nat -> re_fd (nth i es relay_remove_b_c.no_entry) = FD ->
   re_eof (nth i es relay_remove_b_c.no_entry) = 0 -> dr_src_ok B RG ly S W mem (nth i es relay_remove_b_c.no_entry) h j) ->
arelay_at B RG ly S1 W m1 G0 es /\ aout_at B RG ly S1 W m1 c O mx (Z.of_nat (length O)) cap out /\
awake_at RG W m1 /\ (forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W mem W m1 a) /\
(forall i, (i < length es)%nat -> re_fd (nth i es relay_remove_b_c.no_entry) = FD ->
   re_eof (nth i es relay_remove_b_c.no_entry) = 0 -> dr_src_ok B RG ly S1 W m1 (nth i es relay_remove_b_c.no_entry) h j).
Proof.
intros ly S S1 HpA HpB W mem md m1 md1 G0 es c O mx cap out h j FD X HAR HAR1 Eab KV PR HX RGP HREL HOUT HWAKE HSRC.
pose proof RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
assert (K : forall a, brp_wt ly S a -> ~ brp_lkw a -> abyte_kept W mem W m1 a).
{ intros a Hw Hl. split; [apply KV; [exact Hw | intros Hx; exact (Hl (HX a Hx))]|].
  destruct Hw as [(Hi & _) | (p & n & Hin & Ha)].
  - unfold arm. apply writable_kept. intros Hp. exact (PR a Hi Hp).
  - intros _. unfold arm. apply (apresent_writable SEGS). rewrite <- Eab in Hin.
    destruct (alx_blocks _ _ _ LAWS _ _ _ _ _ _ p n HAR1 Hin) as (_ & _ & _ & _ & Hpr & _). exact (proj1 (Hpr a Ha)). }
assert (KB : forall p n a, In (p, n) (ablocks B ly S) -> p <= a < p + n -> abyte_kept W mem W m1 a).
{ intros p n a Hin Ha. apply K; [exact (brp_wt_blk ly S p n a Hin Ha)|]. intros Hl.
  assert (Hn : 0 <= n) by lia. pose proof (req_size_pos n Hn) as (_ & Hrq).
  assert (Hpa : p <= a < p + req_size n) by lia.
  apply (proj2 (alx_client_img _ _ _ LAWS ly S HpA W mem md a HAR (or_introl (ex_intro _ p (ex_intro _ n (conj Hin Hpa)))))).
  apply RGIMG. unfold rg_rng. left. unfold brp_lkw in Hl. lia. }
assert (KR : forall a, rg_rng RG a -> ~ brp_lkw a -> abyte_kept W mem W m1 a).
{ intros a Ha Hl. destruct (RGIMG a Ha) as (Hi & Ho & _). apply K; [left; split; assumption | exact Hl]. }
assert (KG : forall x n a, In (x, n) (G_RR B RG) -> x <= a < x + n -> ~ brp_lkw a -> abyte_kept W mem W m1 a).
{ intros x n a Hin Ha Hl. destruct (HG a) as (Hi & Ho & _).
  { unfold inG. apply Exists_exists. exists (x, n). split; [exact Hin | unfold in_zr; cbn [fst snd]; lia]. }
  apply K; [left; split; assumption | exact Hl]. }
assert (KI : forall a, in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) -> ~ brp_lkw a -> abyte_kept W mem W m1 a).
{ intros a Ha Hl. apply K; [left; exact Ha | exact Hl]. }
(* g_lock's word apart from each cell, one quantified fact per cell (no disjunction left in the context) *)
pose proof HRGP as (HLK & _). cbn [zall_disjoint] in HLK. unfold zdisj in HLK. cbn [fst snd] in HLK.
destruct HLK as (D_s & D_src & D_nsrc & D_capsrc & D_smax & D_nout & D_capout & D_out & D_client & D_cbr & D_sdead
  & D_seintr & D_wake & D_errno & _).
assert (N_s : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_s; clear; lia).
assert (N_src : forall a, rg_src RG <= a < rg_src RG + 8 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_src; clear; lia).
assert (N_nsrc : forall a, rg_nsrc RG <= a < rg_nsrc RG + 4 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_nsrc; clear; lia).
assert (N_capsrc : forall a, rg_capsrc RG <= a < rg_capsrc RG + 4 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_capsrc; clear; lia).
assert (N_smax : forall a, rg_send_max RG <= a < rg_send_max RG + 8 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_smax; clear; lia).
assert (N_nout : forall a, rg_nout RG <= a < rg_nout RG + 8 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_nout; clear; lia).
assert (N_capout : forall a, rg_capout RG <= a < rg_capout RG + 8 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_capout; clear; lia).
assert (N_out : forall a, rg_out RG <= a < rg_out RG + 8 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_out; clear; lia).
assert (N_client : forall a, rg_client RG <= a < rg_client RG + 4 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_client; clear; lia).
assert (N_cbr : forall a, rg_client_broken RG <= a < rg_client_broken RG + 1 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_cbr; clear; lia).
assert (N_sdead : forall a, rg_send_dead RG <= a < rg_send_dead RG + 1 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_sdead; clear; lia).
assert (N_seintr : forall a, rg_send_eintr RG <= a < rg_send_eintr RG + 1 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_seintr; clear; lia).
assert (N_wake : forall a, rg_wake RG + 4 <= a < rg_wake RG + 8 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_wake; clear; lia).
assert (N_errno : forall a, as_errno B <= a < as_errno B + 4 -> ~ brp_lkw a) by (intros a Ha; unfold brp_lkw; revert Ha D_errno; clear; lia).
clear D_s D_src D_nsrc D_capsrc D_smax D_nout D_capout D_out D_client D_cbr D_sdead D_seintr D_wake D_errno.
split.
{ apply (arelay_at_kept B RG ly S W mem ly S1 W m1 G0 es HREL).
  - intros r Hr a Ha. unfold arelay_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | Hr]]]]; cbn [fst snd] in Ha.
    + apply KR; [unfold rg_rng; tauto | exact (N_src a Ha)].
    + apply KR; [unfold rg_rng; tauto | exact (N_nsrc a Ha)].
    + apply KI; [exact (HRGI a (or_introl Ha)) | exact (N_capsrc a Ha)].
    + pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & HGin & _). exact (KB G0 ATABLE a HGin Ha).
    + apply in_concat in Hr as (l & Hl & Hr). apply in_map_iff in Hl as (e & <- & He).
      pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEN & _). rewrite Forall_forall in HEN.
      destruct (proj1 (brp_entry_fp ly S W mem e (HEN e He)) r Hr a Ha) as (p & n & Hin & Hpa).
      exact (KB p n a Hin Hpa).
  - intros b Hb. rewrite Eab. unfold arelay_blks in Hb. destruct Hb as [<- | Hb].
    + pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & HGin & _). exact HGin.
    + apply in_concat in Hb as (l & Hl & Hb). apply in_map_iff in Hl as (e & <- & He).
      pose proof HREL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HEN & _). rewrite Forall_forall in HEN.
      exact (proj2 (brp_entry_fp ly S W mem e (HEN e He)) b Hb). }
split.
{ apply (aout_at_kept B RG ly S W mem ly S1 W m1 c O mx (Z.of_nat (length O)) cap out HOUT).
  - intros r Hr a Ha. unfold aout_fp in Hr. cbn [In] in Hr.
    destruct Hr as [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | [<- | Hr]]]]]]]]]; cbn [fst snd] in Ha.
    + apply KI; [exact (HRGI a (or_intror (or_introl Ha))) | exact (N_smax a Ha)].
    + apply (KG (rg_nout RG) 8 a); [unfold G_RR, G_DR, G_SL; brp_in | exact Ha | exact (N_nout a Ha)].
    + apply (KG (rg_capout RG) 8 a); [unfold G_RR, G_DR, G_SL; brp_in | exact Ha | exact (N_capout a Ha)].
    + apply (KG (rg_out RG) 8 a); [unfold G_RR, G_DR, G_SL; brp_in | exact Ha | exact (N_out a Ha)].
    + apply KI; [exact (HRGI a (or_intror (or_intror (or_introl Ha)))) | exact (N_client a Ha)].
    + apply (KG (rg_client_broken RG) 1 a); [unfold G_RR, G_DR, G_SL; brp_in | exact Ha | exact (N_cbr a Ha)].
    + apply KI; [exact (HRGI a (or_intror (or_intror (or_intror Ha)))) | exact (N_sdead a Ha)].
    + apply (KG (rg_send_eintr RG) 1 a); [unfold G_RR, G_DR, G_SL; brp_in | exact Ha | exact (N_seintr a Ha)].
    + apply (KG (as_errno B) 4 a); [unfold G_RR, G_DR, G_SL; brp_in | exact Ha | exact (N_errno a Ha)].
    + destruct (cap =? 0) eqn:Hc0; cbn [In] in Hr; [destruct Hr|]. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
      pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
      destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia|].
      exact (KB out cap a Hin Ha).
  - intros b Hb. rewrite Eab. unfold aout_blks in Hb. destruct (cap =? 0) eqn:Hc0; [destruct Hb|].
    destruct Hb as [<- | []].
    pose proof HOUT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hblk).
    destruct Hblk as [(Hc & _) | (_ & _ & Hin & _)]; [apply Z.eqb_neq in Hc0; lia | exact Hin]. }
split.
{ apply (awake_at_kept RG W mem W m1 HWAKE). intros r Hr a Ha. destruct Hr as [<- | []]. cbn [fst snd] in Ha.
  apply KR; [unfold rg_rng; tauto | exact (N_wake a Ha)]. }
assert (GS : forall a, rg_s RG <= a < rg_s RG + 4 * ASRC -> abyte_kept W mem W m1 a).
{ intros a Ha. apply KR; [unfold rg_rng; tauto | exact (N_s a Ha)]. }
split; [exact GS|].
intros i Hi Hfd Heof. destruct (HSRC i Hi Hfd Heof) as (Hj & HA & HO & R). split; [exact Hj|].
assert (HAr : rg_s RG <= rg_s RG + ASRC * Z.of_nat j /\ rg_s RG + ASRC * Z.of_nat j + ASRC <= rg_s RG + 4 * ASRC)
by (unfold ASRC; lia).
split.
{ apply (asrc_at_kept B ly S W mem ly S1 W m1 _ h HA).
  - pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ & Hexp & Hheld & _).
    intros r Hr a Ha. unfold asrc_fp in Hr. destruct Hr as [<- | [<- | Hr]].
    + cbn [fst snd] in Ha. apply GS. lia.
    + unfold gfp, bzs in Ha. cbn [fst snd] in Ha. rewrite length_map in Ha.
      pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPJ & _).
      apply (KB (hs_partial h) APARTIAL a Hpb). lia.
    + apply in_app_or in Hr. destruct Hr as [Hr | Hr]; [|apply in_app_or in Hr; destruct Hr as [Hr | Hr]].
      * destruct (proj1 (brp_alist_fp ly S W mem _ _ _ Hpend) r Hr a Ha) as [Hl | (p & n & Hin & Hpa)];
        [apply GS; unfold ASRC in *; lia | exact (KB p n a Hin Hpa)].
      * destruct (proj1 (brp_alist_fp ly S W mem _ _ _ Hexp) r Hr a Ha) as [Hl | (p & n & Hin & Hpa)];
        [apply GS; unfold ASRC in *; lia | exact (KB p n a Hin Hpa)].
      * destruct (proj1 (brp_alist_fp ly S W mem _ _ _ Hheld) r Hr a Ha) as [Hl | (p & n & Hin & Hpa)];
        [apply GS; unfold ASRC in *; lia | exact (KB p n a Hin Hpa)].
  - pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & _ & _ & _ & Hexp & Hheld & _).
    intros b Hb. rewrite Eab. unfold asrc_blks in Hb. destruct Hb as [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb. destruct Hb as [Hb | Hb]; [|apply in_app_or in Hb; destruct Hb as [Hb | Hb]].
    + exact (proj2 (brp_alist_fp ly S W mem _ _ _ Hpend) b Hb).
    + exact (proj2 (brp_alist_fp ly S W mem _ _ _ Hexp) b Hb).
    + exact (proj2 (brp_alist_fp ly S W mem _ _ _ Hheld) b Hb). }
split; [|exact R].
intros i' Hi' Hne. destruct (HO i' Hi' Hne) as (f & o & Vf & Vo & Hfo). exists f, o.
assert (Hi4 : rg_s RG <= rg_s RG + ASRC * Z.of_nat i' /\ rg_s RG + ASRC * Z.of_nat i' + 8 <= rg_s RG + 4 * ASRC)
by (unfold ASRC; lia).
split; [apply (akept_vm W mem); [intros x Hx; apply GS; cbn in Hx; lia | exact Vf]|].
split; [apply (akept_vm W mem); [intros x Hx; apply GS; cbn in Hx; lia | exact Vo] | exact Hfo].
Qed.
(* a value kept by the ASan view is kept in memory *)
Lemma brp_vm_keep : forall (W : world SEGS) m m' a (n : nat) v,
(forall x, a <= x < a + Z.of_nat n -> aview SEGS (w_H W) m' x = aview SEGS (w_H W) m x) ->
val_mem SEGS (arm W m) a n v -> val_mem SEGS (arm W m') a n v.
Proof.
intros W m m' a n v HK HV. unfold arm in *.
apply (val_mem_kept SEGS (w_H W) (w_H W) m m' a n v); [intros k Hk; apply HK; lia | exact HV].
Qed.
(* a register's symbolic value, as a numeral *)
Lemma brp_den : forall E e v, U E e = v -> sv_denot E e = w64 v.
Proof. intros E e v H. unfold w64. rewrite <- H. unfold U. symmetry. apply Z_to_bv_bv_unsigned. Qed.
Lemma brp_off : forall E n c v, ew E n = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> 0 <= v + c < 2 ^ 64 ->
sv_denot E (SOff n c) = w64 (v + c).
Proof. intros E n c v Hn Hv Hc. apply brp_den. exact (U_atom_off E n v c Hn Hv Hc). Qed.
(* the blez at 0x83ef0 and the 56 |es| of 0x83f00-0x83f08: |es| <= 16, so both are decided by cases *)
Ltac brp_n16 Hd := repeat (destruct Hd as [->|Hd]); try (match goal with H : _ = _ |- _ => subst end);
  vm_compute; reflexivity.
Lemma brp_blez : forall (x : word) n, x = Z_to_bv 64 n -> 0 <= n <= 16 ->
branch_taken BC_GE (Z_to_bv 64 0) (sext 64 (bv_extract 0 32 x)) = (n =? 0).
Proof.
intros x n -> Hn.
assert (Hd : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
  n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16) by lia.
brp_n16 Hd.
Qed.
Lemma brp_a2 : forall (x : word) n, x = Z_to_bv 64 n -> 0 <= n <= 16 ->
alu64 ALU_SUB (alu64 ALU_SLL (sext 64 (bv_extract 0 32 x)) (Z_to_bv 64 6))
              (alu64 ALU_SLL (sext 64 (bv_extract 0 32 x)) (Z_to_bv 64 3)) = w64 (AENT * n).
Proof.
intros x n -> Hn. unfold AENT.
assert (Hd : n = 0 \/ n = 1 \/ n = 2 \/ n = 3 \/ n = 4 \/ n = 5 \/ n = 6 \/ n = 7 \/ n = 8 \/ n = 9 \/ n = 10 \/
  n = 11 \/ n = 12 \/ n = 13 \/ n = 14 \/ n = 15 \/ n = 16) by lia.
brp_n16 Hd.
Qed.

(* ---- ROUTE R (a Theorem Labs lane's route-R lift crew, group G8b-relayrm-B; G4's form, lib/B/W_bx_order_x.v): PRO at a world
   relation R, against lib/B/W_relay_remove_cx.v's rr_pro_stmt_xR (R right after ARx).  The walk is the strict one with
   these steps changed: the entry journal -> W_journal_x.v ajournal_gx_init_xR; the runs -> the G runs paj_run_x_xG /
   paj_run_to_x_xG (W_kit_x.v paj_run_tok_xR / paj_run_to_tok_xR); the branch -> W_kit.v paj_branch_xR; the lock ->
   W_sites_x.v aj_gx_entry_at_xR composed by SRrG_bind (it takes the entry's strict contract, so ALOCK stays
   alock_realizes_x); the fd < 0 return -> the strict paj_ret_at, lifted by SRr_SRrG (WLE_R).  No step moves the world
   (the lock's post pins it).  No file-local helper carries a journal or an SRr fact (brp_entry, brp_carry,
   brp_alock_carry and the footprint lemmas read the entry and one later memory of the same world), so none gets a twin.
   Census rows (a Theorem Labs lane's G8b-relayrm-B.tsv (sha256 4c7c7e01243b; internal record)) -> twins: :220 AFREE -> AFREE_R, :224 DRAIN -> DRAIN_R,
   :225 GSE -> GSE_R, :227 AFREEN -> AFREEN_R (the spine's Section wR texts; PRO calls none of them, so they vanish
   from rr_pro_xR), :617 rr_pro -> rr_pro_xR.  At R := wle rr_pro_xR is its strict text: rr_pro after the Section is
   rr_pro_xR at wle. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
(* the R free rules' call-boundary premise RO (lib/B/W_relay_remove_cx.v Section wR) *)
Variable RO : (word -> option byte) -> Prop.
(* :220 AFREE at R *)
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* :224 DRAIN, :225 GSE at R (W_contract_xR.v) *)
Hypothesis DRAIN_R : dr_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_drain).
Hypothesis GSE_R : gse_spec_xR B PST ARx R MT RP MMAX RG (BASE + AF_fr_gestures_end).
(* :227 AFREEN at R *)
Hypothesis AFREEN_R : afree_null_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX_AFREE R.
(* the token runners at R: W_journal_x.v's G runs (concluding SRrG SEGS R over ajournal_gx_xR) and the R branch *)
Let RUNG := paj_run_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R (G_RR B RG) HG 0 [].
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* :617 rr_pro *)
Theorem rr_pro_xR : rr_pro_stmt_xR B PST ARx R MT RP MMAX RG.
Proof.
(* the four R callee hypotheses are not PRO's (it calls only the lock): cleared, so that no tactic fills an evar with
   them and rr_pro_xR's premises are R_refl, R_trans and WLE_R *)
clear AFREE_R AFREEN_R DRAIN_R GSE_R RO.
intros [regs ly S Hp W mem md ch G0 FD es j h c O mx cap out rest kr] HB KL KU.
unfold RBASE in HB.
cbn [rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxrest rxkr rsp0 rN rFP rtr rnth] in HB.
destruct HB as (HPRE & H32 & HCNT & RGP & H10 & RFD & HLOCK & HWAKE & HREL & HOUT & HROM & HSRC & HPERM & HTRM & HLIVE & HMOK
  & HRM & HCNTP).
cbn [rxregs rxW rxmem rxmd].
pose proof RGP as RGPx. destruct RGP as (RGLOCK & RGNSRC & RGSRC & RGAL8 & RGAL4 & RGSAL & RGIMG & RGWR & RGSEP).
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
destruct (brp_entry W ly S Hp regs mem md ch HPRE H32) as [HS SHOK].
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
assert (WS : RR_STK_x = 17056) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
assert (HJ : ajournal_gx_xR (SK := SK) SEGS B PST ARx R (G_RR B RG) 0 [] RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out)
  ly S Hp W mem md [] ly S Hp W mem md 0).
{ apply (ajournal_gx_init_xR SEGS B PST ARx R_refl (G_RR B RG) 0 [] RR_STK_x _ ly S Hp W regs mem md ch HPRE);
  [lia | reflexivity | lia | intros a Ha; lia]. }
remember (Eimg (Ereg regs brp_extra)) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
by (intros n r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (E32 : ew E 32 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
assert (HAE : env_agree 32 (Ereg regs brp_extra) E) by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
clear HE.
assert (WB : alloc_ceiling + 17056 <= spZ regs) by lia.
assert (E10 : sv_denot E (SOff 10 0) = Z_to_bv 64 FD)
by (cbn [sv_denot]; rewrite (EE 10%nat 10%bv eq_refl), H10; rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
unfold cfg_at. change (w64 A_rr_entryP) with (Z_to_bv 64 A_rr_entryP). unfold A_rr_entryP, A_rr_entry.
(* 0x841fc-0x84214: the frame and the six saves, to the fd test 0x84218 *)
paj_run_tok_xR RUNG HS HJ SHOK brp_Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
brp_grab.
assert (KV1 : forall a, brp_wt ly S a -> aview SEGS (w_H W) (ms_mem ms) a = aview SEGS (w_H W) mem a).
{ apply (brp_kv_run E _ W mem mem (ms_mem ms) (brp_wt ly S) (fun a _ => eq_refl) HFr).
  intros a Hw. pose proof (brp_wt_lo ly S Hp W mem md a HAR Hw) as WA. brp_nowin WA WB. }
pose proof (brp_pres_grow (w_H W) mem mem (ms_mem ms) (fun a _ Ha => Ha) HGr) as PRES. clear HFr HGr.
psrr_branch_tok RUNG BRR HS SHOK brp_Bspan.
-
(* fd < 0: the epilogue 0x842b8 and the return; nothing changed *)
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hc1 end.
assert (Hneg : FD < 0).
{ cbn [branch_taken] in Hc1. rewrite E10, bv_lts_signed in Hc1. apply Z.ltb_lt in Hc1.
  rewrite (brp_fd_signed FD RFD) in Hc1. change (bv_signed (sv_denot E (SLit 0))) with 0 in Hc1. exact Hc1. }
clear Hc1.
paj_run_tok_xR RUNG HS HJ SHOK brp_Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
brp_grab.
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ ?m2) =>
assert (KV2 : forall a, brp_wt ly S a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a) end.
{ apply (brp_kv_run E _ W mem _ _ (brp_wt ly S) KV1 HFr).
  intros a Hw. pose proof (brp_wt_lo ly S Hp W mem md a HAR Hw) as WA. brp_nowin WA WB. }
pose proof (brp_pres_grow (w_H W) mem _ _ PRES HGr) as PRES2. clear PRES HFr HGr KV1. rename PRES2 into PRES.
prreg HS (1%bv : bv 5) Rr1.
(* the return: the strict ret step, lifted to R (WLE_R) *)
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold rPOST_xR, rr_post_xR.
cbn [rxregs rxly rxS rxHp rxW rxmem rxmd rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxkr].
lazymatch goal with |- exists _ _ _ _ _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists ly, S, Hp, r, m, d end.
eexists.
split; [cbn [ms_regs]; rewrite Rr1, (EE 1%nat 1%bv eq_refl), Hra; reflexivity|].
rewrite ?wvb_collapse in HJ.
split; [eapply ajournal_gx_materialize_xR; first [exact HJ | exact LAWS | exact Hsegs]|].
split. { eapply (aregs_preserved_of_st_ok SEGS _ E _ _ regs brp_extra HS); [exact HAE | vm_compute; reflexivity]. }
split. { intros a Hi _ _ Ha. exact (PRES a Hi Ha). }
split. { unfold rr_tr. rewrite (proj2 (Z.ltb_lt FD 0) Hneg). exact (mo_le_refl MT MLAW S). }
(* the room round: kr is below RBASE's budget (RMM_of); the state is the entry's (no fake frame) *)
split. { eapply (RMM_of RP S kr); [|exact HRM]. lia. }
destruct (brp_carry ly S S Hp Hp W mem md _ _ G0 es c O mx cap out h j FD (fun _ => False)
  HAR (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) eq_refl (fun a Hw _ => KV2 a Hw) PRES
  (fun a (f : False) => match f with end) RGPx HREL HOUT HWAKE HSRC)
  as (CREL & COUT & CWAKE & CGS & _).
split. { exact (brp_alock_carry ly S W mem _ (fun _ => False) false (fun a Hw _ => KV2 a Hw) PRES (fun a _ f => f) RGPx HLOCK). }
split. { exact CWAKE. }
split. { intros a Ha _. exact (CGS a Ha). }
split. { intros _. split; [exact CREL|]. split; [exact COUT|]. apply Permutation_refl. }
intros i Hi Hge. lia.
-
(* fd >= 0: s0 = fd, s2 = the shadow offset, a0 = &g_lock, pthread_mutex_lock (0x84234) *)
lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hc1 end.
assert (Hpos : 0 <= FD).
{ cbn [branch_taken] in Hc1. rewrite E10, bv_lts_signed in Hc1. apply Z.ltb_ge in Hc1.
  rewrite (brp_fd_signed FD RFD) in Hc1. change (bv_signed (sv_denot E (SLit 0))) with 0 in Hc1. exact Hc1. }
clear Hc1.
paj_run_tok_xR RUNG HS HJ SHOK brp_Bspan. { apply awr_ok_x_of0. awr_ok_tac. exact Usp. }
brp_grab.
lazymatch type of HFr with frame_of _ _ _ (mrestrict _ ?m2) =>
assert (KV2 : forall a, brp_wt ly S a -> aview SEGS (w_H W) m2 a = aview SEGS (w_H W) mem a) end.
{ apply (brp_kv_run E _ W mem _ _ (brp_wt ly S) KV1 HFr).
  intros a Hw. pose proof (brp_wt_lo ly S Hp W mem md a HAR Hw) as WA. brp_nowin WA WB. }
pose proof (brp_pres_grow (w_H W) mem _ _ PRES HGr) as PRES2. clear PRES HFr HGr KV1. rename PRES2 into PRES.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
(* the six saves, read off the frame's region before the call *)
assert (EEb : forall n (r : bv 5), (n < 32)%nat -> Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
  by (intros n r Hn Hr; exact (EE n r Hr)).
pose proof (st_ok_region_nth _ _ _ 0%nat _ HS eq_refl) as HRstk.
cbn [ms_mem restrict] in HRstk.
eassert (HSV0 : forall i, (i < 6)%nat -> val_mem SEGS (arm W _) (spZ regs - RR_FRAME + 8 * Z.of_nat i) 8
  (bv_unsigned (getr regs (nth i RR_SAVED 0%bv)))).
{ rewrite <- Usp. apply (brp_saved_of_region E W _ regs _ _ _ _ _ HRstk); [|exact EEb].
  intros i Hi. do 6 (destruct i as [|i]; [cbn [nth brp_saved_atoms Z.of_nat]; cbn [In]; brp_in|]). lia. }
clear HRstk.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18.
prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (23%bv : bv 5) Q23. prreg HS (24%bv : bv 5) Q24.
prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26. prreg HS (27%bv : bv 5) Q27.
assert (HSPc : spZ (ms_regs msC) = spZ regs + -48).
{ unfold spZ at 1. rewrite Q2, Usp. apply unsigned_lit_small. unfold spZ in *. lia. }
assert (Lr2 : getr (ms_regs msC) 2 = w64 (spZ regs - RR_FRAME)) by (rewrite Q2, Usp; unfold w64, RR_FRAME; f_equal; lia).
assert (Lr8 : getr (ms_regs msC) 8 = w64 FD) by (rewrite Q8, (EE 10%nat 10%bv eq_refl); exact H10).
assert (Lr18 : getr (ms_regs msC) 18 = w64 SHADOW_OFF) by (rewrite Q18, E32; rewrite <- SB_SHADOW_OFF; reflexivity).
assert (L3 : getr (ms_regs msC) 3 = getr regs 3) by (rewrite Q3; exact (EE 3%nat 3%bv eq_refl)).
assert (L4 : getr (ms_regs msC) 4 = getr regs 4) by (rewrite Q4; exact (EE 4%nat 4%bv eq_refl)).
assert (L21 : getr (ms_regs msC) 21 = getr regs 21) by (rewrite Q21; exact (EE 21%nat 21%bv eq_refl)).
assert (L22 : getr (ms_regs msC) 22 = getr regs 22) by (rewrite Q22; exact (EE 22%nat 22%bv eq_refl)).
assert (L23 : getr (ms_regs msC) 23 = getr regs 23) by (rewrite Q23; exact (EE 23%nat 23%bv eq_refl)).
assert (L24 : getr (ms_regs msC) 24 = getr regs 24) by (rewrite Q24; exact (EE 24%nat 24%bv eq_refl)).
assert (L25 : getr (ms_regs msC) 25 = getr regs 25) by (rewrite Q25; exact (EE 25%nat 25%bv eq_refl)).
assert (L26 : getr (ms_regs msC) 26 = getr regs 26) by (rewrite Q26; exact (EE 26%nat 26%bv eq_refl)).
assert (L27 : getr (ms_regs msC) 27 = getr regs 27) by (rewrite Q27; exact (EE 27%nat 27%bv eq_refl)).
assert (QA0 : getr (ms_regs msC) 10 = w64 (rg_lock RG)).
{ rewrite Q10. change 244%nat with (A_OBJ 3).
  rewrite (img_env_atomP E (A_OBJ 3) HEI ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), RGLOCK. reflexivity. }
pose proof (pa_obj_img 3 ltac:(lia)) as HlkR. rewrite <- RGLOCK in HlkR.
assert (LKc : alock_at RG W (ms_mem msC) false)
  by (exact (brp_alock_carry ly S W mem _ (fun _ => False) false (fun a Hw _ => KV2 a Hw) PRES (fun a _ f => f) RGPx HLOCK)).
pose proof LKc as (LK0 & LK4 & LK8 & LKW). unfold arm in LK0, LK4, LK8, LKW.
assert (LKV : forall a, rg_lock RG <= a < rg_lock RG + 12 -> aview SEGS (w_H W) (ms_mem msC) a <> None).
{ intros a Ha. unfold aview.
  destruct (Z_lt_ge_dec a (rg_lock RG + 4)) as [h1|h1]; [|destruct (Z_lt_ge_dec a (rg_lock RG + 8)) as [h2|h2]].
  - pose proof (LK0 (Z.to_nat (a - rg_lock RG)) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + (a - rg_lock RG)) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK4 (Z.to_nat (a - (rg_lock RG + 4))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 4 + (a - (rg_lock RG + 4))) with a in X by lia. rewrite X. discriminate.
  - pose proof (LK8 (Z.to_nat (a - (rg_lock RG + 8))) ltac:(lia)) as X. rewrite Z2Nat.id in X by lia.
    replace (rg_lock RG + 8 + (a - (rg_lock RG + 8))) with a in X by lia. rewrite X. discriminate. }
assert (LKtb : aview SEGS (w_H W) (ms_mem msC) (rg_lock RG) = Some 0).
{ unfold aview. pose proof (LK0 0%nat ltac:(lia)) as X. cbn [Z.of_nat] in X.
  rewrite Z.add_0_r in X. rewrite X. vm_compute. reflexivity. }
pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HARl.
assert (HNOWN : forall a, rg_lock RG <= a < rg_lock RG + 12 -> ~ aowned B ly S a).
{ intros a Ha Ho. destruct (RGIMG a ltac:(unfold rg_rng; left; exact Ha)) as (Hi & Hno & _).
  apply Hno. exact (proj1 (alx_owned_image _ _ _ LAWS ly S Hp W (ms_mem msC) _ a HARl Hi) Ho). }
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R (G_RR B RG) 0 [] ESTACK (SIGMA WS_pthread_mutex_lock)
    (fun a => rg_lock RG + 4 <= a < rg_lock RG + 8)
    (fun (_ : bvmap 5 word) (mem' : word -> option byte) => val_mem SEGS (mrestrict (w_H W) mem') (rg_lock RG + 4) 4 16)
    W _ _ RR_STK_x (spZ regs) (rr_fp G0 FD es h cap out) ly S Hp W mem md _ _ _ _ _ _ (-48) _ HG eq_refl HJ).
  - exact HSPc.
  - reflexivity.
  - lia.
  - lia.
  - rewrite WS, Hes. lia.
  - rewrite Q3, (EE 3%nat 3%bv eq_refl). exact Hgp.
  - rewrite Q4, (EE 4%nat 4%bv eq_refl). exact Htp.
  - exact Q1.
  - apply ret_ok_codeptr_v; [lia | reflexivity].
  - intros a. destruct (Z_lt_ge_dec a (rg_lock RG + 4)); [right; lia|].
    destruct (Z_lt_ge_dec a (rg_lock RG + 8)); [left; lia | right; lia].
  - intros a Ha _. exact (LKV a ltac:(lia)).
  - intros a Ha HnG. exfalso. apply HnG. unfold G_RR. apply inG_cons. left. unfold in_zr. cbn [fst snd]. lia.
  - intros HPRE2 HSC. apply (ALOCK _ _ _ _ _ _ _ (rg_lock RG) 0 HPRE2).
    + exact QA0.
    + lia.
    + pose proof (Z.div_mod (rg_lock RG) 8 ltac:(lia)). pose proof (Z.div_mod (rg_lock RG) 4 ltac:(lia)).
      pose proof (Z.mod_pos_bound (rg_lock RG) 4 ltac:(lia)). lia.
    + lia.
    + exact LKtb.
    + reflexivity.
    + exact LK4.
    + intros a Ha. split; [exact (LKV a ltac:(lia))|]. rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + intros a Ha. split; [|split].
      * apply (RGWR (w_H W) (ms_mem msC) a); [left; lia|].
        apply (hidden_not_img SEGS W (Z_to_bv 64 a)). rewrite unsigned_lit_small by lia.
        exact (proj1 (RGIMG a ltac:(unfold rg_rng; left; lia))).
      * exact (HNOWN a ltac:(lia)).
      * rewrite HSPc. unfold ESTACK. unfold spZ in *. lia.
    + (* QMm W1 (B engine 9015b6a6f732): the lock word is in G_RR, and gx_ok's kept clause puts it off as_kept *)
      intros a Ha HK. exact (proj2 (proj2 (HG a ltac:(unfold G_RR; apply inG_cons; left; unfold in_zr; cbn [fst snd]; lia))) (proj1 (proj2 HK))). }
cbv beta. intros W3 c3 _ (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & HLK3 & Hfr3 & Hpres3).
(* the bytes the walk reads, kept by the lock (which writes g_lock's lock word and its scratch only) *)
assert (KV3 : forall a, brp_wt ly S a -> ~ brp_lkw a -> aview SEGS (w_H W) mem3 a = aview SEGS (w_H W) mem a).
{ intros a Hw Hl. pose proof (brp_wt_lo ly S Hp W mem md a HAR Hw) as WA.
  rewrite (Hfr3 a ltac:(revert WA; pose proof asan_consts as (Cx & _); revert Cx; clear; intros; lia) ltac:(exact Hl)
    ltac:(revert WA WB; clear; unfold ESTACK; intros; lia)).
  exact (KV2 a Hw). }
pose proof (fun a Hi Ha => Hpres3 a (PRES a Hi Ha)) as PRES3. clear PRES. rename PRES3 into PRES.
pose proof (ajournal_gx_AR_xR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ3) as HAR3.
destruct (brp_carry ly S S Hp Hp W mem md mem3 md3 G0 es c O mx cap out h j FD brp_lkw HAR HAR3 eq_refl KV3 PRES
  (fun a (Hx : brp_lkw a) => Hx) RGPx HREL HOUT HWAKE HSRC) as (CREL & COUT & CWAKE & CGS & CSRC).
(* the base registers at regs3: the lock keeps the callee-saved ones *)
assert (M2 : getr regs3 2 = w64 (spZ regs - RR_FRAME)) by (etransitivity; [apply (HP3 2 ltac:(unfold acallee_saved; lia)) | exact Lr2]).
assert (M8 : getr regs3 8 = w64 FD) by (etransitivity; [apply (HP3 8 ltac:(unfold acallee_saved; lia)) | exact Lr8]).
assert (M18 : getr regs3 18 = w64 SHADOW_OFF) by (etransitivity; [apply (HP3 18 ltac:(unfold acallee_saved; lia)) | exact Lr18]).
assert (M3 : getr regs3 3 = getr regs 3) by (etransitivity; [apply (HP3 3 ltac:(unfold acallee_saved; lia)) | exact L3]).
assert (M4 : getr regs3 4 = getr regs 4) by (etransitivity; [apply (HP3 4 ltac:(unfold acallee_saved; lia)) | exact L4]).
assert (M21 : getr regs3 21 = getr regs 21) by (etransitivity; [apply (HP3 21 ltac:(unfold acallee_saved; lia)) | exact L21]).
assert (M22 : getr regs3 22 = getr regs 22) by (etransitivity; [apply (HP3 22 ltac:(unfold acallee_saved; lia)) | exact L22]).
assert (M23 : getr regs3 23 = getr regs 23) by (etransitivity; [apply (HP3 23 ltac:(unfold acallee_saved; lia)) | exact L23]).
assert (M24 : getr regs3 24 = getr regs 24) by (etransitivity; [apply (HP3 24 ltac:(unfold acallee_saved; lia)) | exact L24]).
assert (M25 : getr regs3 25 = getr regs 25) by (etransitivity; [apply (HP3 25 ltac:(unfold acallee_saved; lia)) | exact L25]).
assert (M26 : getr regs3 26 = getr regs 26) by (etransitivity; [apply (HP3 26 ltac:(unfold acallee_saved; lia)) | exact L26]).
assert (M27 : getr regs3 27 = getr regs 27) by (etransitivity; [apply (HP3 27 ltac:(unfold acallee_saved; lia)) | exact L27]).
(* the frame's six saves and g_lock held, at mem3 *)
assert (SPhi : spZ regs <= 2 ^ 47) by (revert Hshi H47; clear; intros; lia).
assert (SPlo : 0 <= spZ regs - RR_FRAME < 2 ^ 64)
  by (revert SPhi WB; pose proof asan_consts as (Cz & _); revert Cz; unfold RR_FRAME; clear; intros; lia).
assert (HSV1 : forall i, (i < 6)%nat -> val_mem SEGS (arm W mem3) (spZ regs - RR_FRAME + 8 * Z.of_nat i) 8
  (bv_unsigned (getr regs (nth i RR_SAVED 0%bv)))).
{ intros i Hi. apply (brp_vm_keep W (ms_mem msC) mem3); [|exact (HSV0 i Hi)].
  intros x Hx. apply Hfr3;
  [ revert Hx Hi SPhi WB; unfold RR_FRAME; pose proof asan_consts as (Cz & _); revert Cz; clear; intros; lia
  | revert Hx HlkR WB; unfold RR_FRAME; pose proof asan_consts as (Cz & _); revert Cz; clear; intros; lia
  | revert Hx; unfold RR_FRAME, ESTACK; clear; intros; lia ]. }
assert (LKt : alock_at RG W mem3 true).
{ split; [|split; [exact HLK3 | split]].
  - apply (brp_vm_keep W (ms_mem msC) mem3); [|exact LK0].
    intros x Hx. apply Hfr3; [revert Hx HlkR; clear; intros; lia | revert Hx; clear; intros; lia
    | revert Hx HlkR WB; pose proof asan_consts as (Cz & _); revert Cz; unfold ESTACK, RR_FRAME; clear; intros; lia].
  - apply (brp_vm_keep W (ms_mem msC) mem3); [|exact LK8].
    intros x Hx. apply Hfr3; [revert Hx HlkR; clear; intros; lia | revert Hx; clear; intros; lia
    | revert Hx HlkR WB; pose proof asan_consts as (Cz & _); revert Cz; unfold ESTACK, RR_FRAME; clear; intros; lia].
  - intros i Hi. unfold arm. apply (RGWR (w_H W) mem3 (rg_lock RG + i)); [left; lia|].
    apply (hidden_not_img SEGS W). rewrite unsigned_lit_small by lia.
    exact (proj1 (RGIMG (rg_lock RG + i) ltac:(unfold rg_rng; left; lia))). }
(* ---- the seat at 0x84238: only g_nsrc and g_src are read, and nothing is written ---- *)
pose proof CREL as (CV8 & CW8 & CV4 & CW4 & CV4c & CW4c & Clen & CGin & Ctab & Cok & Cnd).
pose proof (pa_obj_img 4 ltac:(lia)) as Ho4. pose proof (pa_obj_img 5 ltac:(lia)) as Ho5.
pose proof (pa_val_range (A_OBJ 4)) as PV4. pose proof (pa_val_range (A_OBJ 5)) as PV5.
pose proof HRGP as (_ & _ & (Dsn & _) & _). unfold zdisj in Dsn. cbn [fst snd] in Dsn.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem3 md3 G0 ATABLE HAR3 CGin) as (HG16 & HG4096 & HGceil & _).
change (req_size ATABLE) with 896 in HGceil.
remember (Eimg (Ereg regs3 (brp_hextra (Z.of_nat (length es)) G0))) as En eqn:HEn.
assert (HEIn : img_env VAL A_LIM En) by (subst En; apply Eimg_env).
assert (HAEn : env_agree 32 (Ereg regs3 (brp_hextra (Z.of_nat (length es)) G0)) En)
  by (rewrite HEn; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (En32 : ew En 32 = Z_to_bv 64 (Z.of_nat (length es)))
  by (subst En; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 0)).
assert (En33 : ew En 33 = Z_to_bv 64 G0)
  by (subst En; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs3 _ 1)).
assert (EEn : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew En n = getr regs3 r)
  by (intros n r Hn; subst En; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
      rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
assert (En4 : ew En (A_OBJ 4) = Z_to_bv 64 (VAL (A_OBJ 4)))
  by (apply img_env_atomP; [exact HEIn | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (En5 : ew En (A_OBJ 5) = Z_to_bv 64 (VAL (A_OBJ 5)))
  by (apply img_env_atomP; [exact HEIn | unfold A_OBJ, A_TEXT, A_LIM; lia]).
assert (HSn : st_ok_pi SEGS VAL En brp_ssh
  (restrict (w_H W) (mkst regs3 (Z_to_bv 64 (BASE + brp_held)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold brp_ssh. apply pa_entry_st_ok_full.
  - subst En. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - unfold brp_hregions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    + rewrite En4, unsigned_lit_small by lia. rewrite <- RGNSRC.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS En _ (rg_nsrc RG) 0 4 (SOff 32 0) (Z.of_nat (length es)));
      [cbn [sv_denot]; rewrite En32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact CV4.
    + rewrite En5, unsigned_lit_small by lia. rewrite <- RGSRC.
      split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      constructor; [|constructor].
      apply (chunk_ok_val SEGS En _ (rg_src RG) 0 8 (SOff 33 0) G0);
      [cbn [sv_denot]; rewrite En33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | cbn; lia | cbn; lia |].
      rewrite Z.add_0_r. exact CV8.
  - apply pairwise_disjoint_of_extents. unfold brp_hregions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val].
    rewrite En4, En5, !unsigned_lit_small by lia. rewrite <- RGNSRC, <- RGSRC.
    cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
    repeat split; first [exact I | revert Dsn; clear; intros; lia].
  - unfold facts_ok; cbn; tauto. }
assert (SHOKn : sh_ok SEGS brp_hBx [] En (mrestrict (w_H W) mem3)) by (unfold sh_ok; constructor).
clear HEn HS SHOK.
assert (HNle : 0 <= Z.of_nat (length es) <= 16) by (revert Clen; clear; intros; lia).
(* 0x84238-0x8423c: s1 = &g_nsrc's image, a0 = g_nsrc, to the blez 0x84240 *)
paj_run_tok_xR RUNG HSn HJ3 SHOKn brp_Bspan. { brp_awr0. }
brp_mem Em1.
psrr_branch_tok RUNG BRR HSn SHOKn brp_Bspan.
+ (* g_nsrc <= 0: the table is empty, to the unlock tail 0x843c0 with RRU None *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hc3 end.
  cbn [sv_denot] in Hc3. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, En32 in Hc3.
  rewrite (brp_blez _ (Z.of_nat (length es)) eq_refl HNle) in Hc3. apply Z.eqb_eq in Hc3.
  assert (Hnil : es = []) by (destruct es; [reflexivity | cbn [length] in Hc3; lia]).
  paj_run_to_tok_xR RUNTOG HSn HJ3 SHOKn brp_Bspan (AF_fr_relay_remove + 0x1c4). { brp_awr0. }
  brp_mem Em2.
  lazymatch type of HSn with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into msU end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ BRP_KEPT HSn HAEn ltac:(vm_compute; reflexivity)) as HKr.
  cbn [ms_regs restrict] in HKr.
  pmkst HSn. rewrite Em2, Em1 in HJ3 |- *. rewrite ?wvb_collapse in HJ3.
  apply KU. unfold RRU_xR, rregs_base, RHELD_xR, RLIVE_xR, rr_saved.
  cbn [rsp0 rN rFP rtr rnth rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxrest rxkr].
  eexists _, ly, S, Hp, mem3, _, _.
  split; [reflexivity|].
  split.
  { split; [unfold spZ; rewrite (HKr 2%bv ltac:(cbv; tauto)), M2; unfold w64; apply unsigned_lit_small;
          unfold RR_FRAME in SPlo |- *; exact SPlo|].
    split; [rewrite (HKr 3%bv ltac:(cbv; tauto)); exact M3|].
    split; [rewrite (HKr 4%bv ltac:(cbv; tauto)); exact M4|].
    apply brp_s5s11;
    [ rewrite (HKr 21%bv ltac:(cbv; tauto)); exact M21 | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact M22
    | rewrite (HKr 23%bv ltac:(cbv; tauto)); exact M23 | rewrite (HKr 24%bv ltac:(cbv; tauto)); exact M24
    | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact M25 | rewrite (HKr 26%bv ltac:(cbv; tauto)); exact M26
    | rewrite (HKr 27%bv ltac:(cbv; tauto)); exact M27 ]. }
  split; [exact Hpos|].
  split.
  { split.
    { split; [exact HJ3|].
      split; [eapply (ajournal_gx_rom_view_xR SEGS B PST ARx);
        first [exact LAWS | exact Hsegs | exact HJ3 | exact HROMO | exact PSTR | exact HROM]|].
      split; [intros a Hi _ _ Ha; exact (PRES a Hi Ha)|].
      split; [exact HSV1|].
      split; [exact LKt | exact CWAKE]. }
    split; [exact CREL|]. split; [exact COUT|].
    split; [exact HPERM|].
    split; [exact CGS|]. split; [exact CSRC|].
    split; [exact (mo_le_refl MT MLAW S)|]. split; [exact HLIVE|].
    (* the room round: the lock keeps S, so RBASE's budget and count fact are RHELD's *)
    split; [exact HRM | exact HCNTP]. }
  rewrite Hnil. intros e He. destruct He.
+ (* g_nsrc > 0: the scan's setup 0x84244-0x84268, to the loop head 0x8426c with RRL 0 *)
  lazymatch goal with H : branch_taken _ _ _ = _ |- _ => rename H into Hc3 end.
  cbn [sv_denot] in Hc3. rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned, En32 in Hc3.
  rewrite (brp_blez _ (Z.of_nat (length es)) eq_refl HNle) in Hc3. apply Z.eqb_neq in Hc3.
  assert (Hne : (0 < length es)%nat) by lia.
  paj_run_to_tok_xR RUNTOG HSn HJ3 SHOKn brp_Bspan (AF_fr_relay_remove + 0x70). { brp_awr0. }
  brp_mem Em2.
  lazymatch type of HSn with st_ok_pi _ _ _ _ (restrict _ ?msx) => rename msx into msL end.
  pose proof (regs_kept_of_st_ok_pi _ _ _ regs3 _ BRP_KEPT HSn HAEn ltac:(vm_compute; reflexivity)) as HKr.
  cbn [ms_regs restrict] in HKr.
  prreg HSn (9%bv : bv 5) N9. prreg HSn (11%bv : bv 5) N11. prreg HSn (12%bv : bv 5) N12.
  prreg HSn (13%bv : bv 5) N13. prreg HSn (14%bv : bv 5) N14. prreg HSn (19%bv : bv 5) N19.
  prreg HSn (20%bv : bv 5) N20.
  change 333%nat with (A_HI 53) in N9. change 334%nat with (A_HI 54) in N20.
  rewrite (img_env_atomP En (A_HI 53) HEIn ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH53 in N9.
  rewrite (img_env_atomP En (A_HI 54) HEIn ltac:(unfold A_HI, A_TEXT, A_LIM; lia)), HH54 in N20.
  rewrite En32, (brp_a2 _ (Z.of_nat (length es)) eq_refl HNle) in N12.
  (* the one-time flags (W_traps.v's seat values): G0 is a live block, 16-aligned and >= 4096 *)
  assert (HG0r : 0 < G0 < 2 ^ 64) by lia.
  assert (HG08 : G0 mod 8 = 0).
  { pose proof (Z.div_mod G0 16 ltac:(lia)) as D. rewrite HG16, Z.add_0_r in D. rewrite D.
    replace (16 * (G0 / 16)) with ((2 * (G0 / 16)) * 8) by ring. apply Z_mod_mult. }
  rewrite En33 in N11, N13, N14. rewrite (trap_w_snez G0 HG0r) in N13. rewrite (trap_w_base_ok G0 HG0r HG08) in N14.
  pmkst HSn. rewrite Em2, Em1 in HJ3 |- *. rewrite ?wvb_collapse in HJ3.
  apply KL. unfold RRL_xR, rregs_held, rregs_base, RHELD_xR, RLIVE_xR, rr_saved.
  cbn [rsp0 rN rFP rtr rnth rxregs rxly rxS rxHp rxW rxmem rxmd rxch rxG0 rxFD rxes rxj rxh rxc rxO rxmx rxcap rxout rxrest rxkr].
  eexists _, ly, S, Hp, mem3, _, _.
  split; [reflexivity|].
  split.
  { split.
    { split; [unfold spZ; rewrite (HKr 2%bv ltac:(cbv; tauto)), M2; unfold w64; apply unsigned_lit_small;
            unfold RR_FRAME in SPlo |- *; exact SPlo|].
      split; [rewrite (HKr 3%bv ltac:(cbv; tauto)); exact M3|].
      split; [rewrite (HKr 4%bv ltac:(cbv; tauto)); exact M4|].
      apply brp_s5s11;
      [ rewrite (HKr 21%bv ltac:(cbv; tauto)); exact M21 | rewrite (HKr 22%bv ltac:(cbv; tauto)); exact M22
      | rewrite (HKr 23%bv ltac:(cbv; tauto)); exact M23 | rewrite (HKr 24%bv ltac:(cbv; tauto)); exact M24
      | rewrite (HKr 25%bv ltac:(cbv; tauto)); exact M25 | rewrite (HKr 26%bv ltac:(cbv; tauto)); exact M26
      | rewrite (HKr 27%bv ltac:(cbv; tauto)); exact M27 ]. }
    split; [rewrite (HKr 8%bv ltac:(cbv; tauto)); exact M8|].
    split; [exact N9|].
    split; [rewrite (HKr 18%bv ltac:(cbv; tauto)); exact M18|].
    exact N20. }
  split; [exact N11|].
  split; [exact N12|].
  split; [exact N13|].
  split; [exact N14|].
  split; [rewrite N19; unfold w64, AENT; reflexivity|].
  split; [exact Hpos|]. split; [exact Hne|].
  split; [intros i Hi; lia|].
  split.
  { split; [exact HJ3|].
    split; [eapply (ajournal_gx_rom_view_xR SEGS B PST ARx);
      first [exact LAWS | exact Hsegs | exact HJ3 | exact HROMO | exact PSTR | exact HROM]|].
    split; [intros a Hi _ _ Ha; exact (PRES a Hi Ha)|].
    split; [exact HSV1|].
    split; [exact LKt | exact CWAKE]. }
  split; [exact CREL|]. split; [exact COUT|].
  split; [exact HPERM|].
  split; [exact CGS|]. split; [exact CSRC|].
  split; [exact (mo_le_refl MT MLAW S)|]. split; [exact HLIVE|].
  split; [exact HRM | exact HCNTP].
Qed.

End wR.
(* the strict text below is the R section's at R := wle (route R's rule: one walk text): the three laws hold for wle *)
Ltac wle_inst := first [ eassumption | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2] ].

Theorem rr_pro : rr_pro_stmt B PST ARx MT RP MMAX RG.
Proof. eapply (rr_pro_xR (@wle SEGS)); wle_inst. Qed.

End c.
End b.
End a.
