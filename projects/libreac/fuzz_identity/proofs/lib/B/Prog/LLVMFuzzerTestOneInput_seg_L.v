(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: restates text of projects/cgif/cgif_file_fuzzer/proofs/lib/YI08.v:162-174, 176-180;
   projects/cgif/cgif_file_fuzzer/proofs/lib/YN13.v:121-125; projects/cgif/cgif_rgb_fuzzer/proofs/lib/YC1n.v:201-203, for
   libreac/fuzz_identity's asan-ubsan build (lib/B). *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_identity/lib/B/Prog/LLVMFuzzerTestOneInput_seg_D1.v, with its addresses and numbers changed; 1003 of its 1137 lines of code are new or changed and 5931 lines of the source are left out. *)
(* Segment L of LLVMFuzzerTestOneInput's ASan+UBSan walk (image B), +0x1bec .. +0x1cd0
   (0x82360 .. 0x82444, 57 slots): the three frees of the output buffers, the use-after-scope
   re-poisoning of the frame's variables, the frame release and the epilogue.

   The code, as offsets from the entry (the neutral listing of fuzz_identity.asan-ubsan):
     +0x1bec  ld a0,184(s1)      dp
     +0x1bf0  jal free           (AFREE4 + HUMF, return +0x1bf4)
     +0x1bf4  mv a0,s5           tk
     +0x1bf8  jal free           (return +0x1bfc)
     +0x1bfc  ld a0,152(s1)      nm
     +0x1c00  jal free           (return +0x1c04)
     +0x1c04 .. +0x1c50          li a0,-8 and nineteen shadow stores at s7 + 44 .. s7 + 81
     +0x1c54  ld s4,16(s1)       the class-4 frame
     +0x1c58  ld a6,64(s1)       the same address
     +0x1c5c .. +0x1c64          the retired-frame magic 0x45e0360e stored at the frame's first word
     +0x1c68  beqz s4,+0x1c84    not taken: the frame address is at least 4096 (HPTR)
     +0x1c6c  li a1,128
     +0x1c70  mv a0,s7
     +0x1c74  jal __asan_set_shadow_f5   (ASSF5; 128 shadow bytes of the frame, return +0x1c78)
     +0x1c78  ld a0,1016(s4)     the flag address the prologue stored there
     +0x1c7c  sb zero,0(a0)      the frame is released (ASF + FFL, through aj_flag_store_pi)
     +0x1c80  j +0x1c90
     +0x1c90  li a0,0
     +0x1c94 .. +0x1ccc          the epilogue: the thirteen callee-saved words and sp
     +0x1cd0  ret
   __asan_set_shadow_00 at +0x1c8c is the machine-stack fallback's release and is not reached.

   The shadow-fill call's journal step is proved here (l_shadow) rather than through
   ajournal_after_write: aset_shadow_realizes (lib/B/Rt/SetShadowDef.v:21) says the call changes
   nothing outside the 128 shadow bytes but not that memory stays present, which
   ajournal_after_write (YCbq.v:520) asks of every address; the journal needs it only on the stack
   window, where apresent_transfer gives it. *)
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require YZ00.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YImgTop.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YN3v YI04 YI09 YI00 YG0s YI16 YO09.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import PaStep.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Reusable Require Import YC5d YM05 YG0p.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.A.Prog Require Import
PaRun PaShadow PaJournal IdentBase IdentRo YC4b YC81.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
IdentBSyms IdentBList IdentBPa IdentBPaLib IdentBFrame IdentBCJ IdentBProgSig YC1g YC1h YC45 YC85.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Rt Require Import SetShadowDef.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.B.Prog Require Import
LLVMFuzzerTestOneInput LLVMFuzzerTestOneInput_inv.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Prog Require SlotModel RcIdentModel.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* YC4b turns lia's division and modulo handling off for every file that loads it; the address
   arithmetic of this segment (shadow_addr) needs it, so this file turns it back on. *)
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.

(* The three return addresses of this segment's free calls, as listing offsets. *)
Definition l_FREE_OFFS : list Z := [0x1bf4; 0x1bfc; 0x1c04].

(* ---- the symbolic states ---------------------------------------------------------------------- *)
(* +0x1bec: the machine frame's slot mf+184 (dp), read-only; atom 32 is dp. *)
Definition l_r1mf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 184 192 184 184 [YP09.mkChunk 184 (CVal 8 (SOff 32 0))].
Definition l_ss1 : sstate := mkSS 0x1bec sr_atoms [l_r1mf] None (mkFacts [] [] []).
(* +0x1bf4: `mv a0,s5`; no memory. *)
Definition l_ss2 : sstate := mkSS 0x1bf4 sr_atoms [] None (mkFacts [] [] []).
(* +0x1bfc: the machine frame's slot mf+152 (nm), read-only; atom 32 is nm. *)
Definition l_r3mf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 152 160 152 152 [YP09.mkChunk 152 (CVal 8 (SOff 32 0))].
Definition l_ss3 : sstate := mkSS 0x1bfc sr_atoms [l_r3mf] None (mkFacts [] [] []).
(* +0x1c04: the shadow stores and the frame header. Atom 32 is the class-4 frame's address, read
   from mf+16 and mf+64; region 1 is its first word (written), region 2 the nineteen shadow bytes
   at s7 + 44 .. s7 + 81. The HPTR fact on atom 32 decides the branch at +0x1c68. *)
Definition l_r4mf : YP09.region :=
  YP09.mkRegion (Some 9%nat) 16 72 16 16
    [YP09.mkChunk 16 (CVal 8 (SOff 32 0)); YP09.mkChunk 64 (CVal 8 (SOff 32 0))].
Definition l_r4sf : YP09.region := YP09.mkRegion (Some 32%nat) 0 8 0 8 [].
Definition l_r4sh : YP09.region := YP09.mkRegion (Some 23%nat) 44 82 44 82 [].
Definition l_ss4 : sstate :=
  mkSS 0x1c04 sr_atoms [l_r4mf; l_r4sf; l_r4sh] None (mkFacts [(32%nat, HPTR 0)] [] []).
(* +0x1c78: the release and the epilogue. Atom 32 is the flag address (held at frame + 1016, read
   through s4); atoms 33 .. 45 are the thirteen callee-saved words of the prologue, at s0 - 8 ..
   s0 - 104. Only the flag byte is written. *)
Definition l_r5fl : YP09.region := YP09.mkRegion (Some 32%nat) 0 1 0 1 [].
Definition l_r5sf : YP09.region :=
  YP09.mkRegion (Some 20%nat) 1016 1024 1016 1016 [YP09.mkChunk 1016 (CVal 8 (SOff 32 0))].
Definition l_r5sv : YP09.region :=
  YP09.mkRegion (Some 8%nat) (-104) 0 0 0
    [YP09.mkChunk (-8) (CVal 8 (SOff 33 0)); YP09.mkChunk (-16) (CVal 8 (SOff 34 0));
     YP09.mkChunk (-24) (CVal 8 (SOff 35 0)); YP09.mkChunk (-32) (CVal 8 (SOff 36 0));
     YP09.mkChunk (-40) (CVal 8 (SOff 37 0)); YP09.mkChunk (-48) (CVal 8 (SOff 38 0));
     YP09.mkChunk (-56) (CVal 8 (SOff 39 0)); YP09.mkChunk (-64) (CVal 8 (SOff 40 0));
     YP09.mkChunk (-72) (CVal 8 (SOff 41 0)); YP09.mkChunk (-80) (CVal 8 (SOff 42 0));
     YP09.mkChunk (-88) (CVal 8 (SOff 43 0)); YP09.mkChunk (-96) (CVal 8 (SOff 44 0));
     YP09.mkChunk (-104) (CVal 8 (SOff 45 0))].
Definition l_ss5 : sstate :=
  mkSS 0x1c78 sr_atoms [l_r5fl; l_r5sf; l_r5sv] None (mkFacts [] [] []).

(* The callee-saved side condition of aregs_preserved, with the register literal computed. *)
Ltac l_cs :=
unfold acallee_saved;
match goal with
| |- context [bv_unsigned ?x] =>
  let v := eval vm_compute in (bv_unsigned x) in change (bv_unsigned x) with v
end; lia.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg identb_listing}.
#[local] Notation SEGS := (@pa_segs _ identb_listing PI).
#[local] Notation VAL := (@pa_val _ identb_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ identb_listing PI).
#[local] Notation BASE := (@pa_val _ identb_listing PI A_TEXT).
Section c.
#[local] Notation rd W mem := (mrestrict (w_H W) mem).
(* The Section of LLVMFuzzerTestOneInput.v / _inv.v, in the same order. *)
Variable B : asyms.
Variable MT : ameter_ops.
Variables XM_LIB XN_LIB : Z -> Z.
Variables RLO RHI : Z.
Variables RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB : Z.
Variable asink_syms_T : Type.
Variable KS : asink_syms_T.
Variable asink_none : list Segment -> asink_syms_T -> (word -> option byte) -> Model -> Prop.
Variable ameta_inv : list Segment -> asink_syms_T -> alayout -> (word -> option byte) -> Z -> Prop.
Variable arodata_okS : list Segment -> asyms -> Z -> Z -> reader -> Prop.
(* What this segment needs, each as the contract's Section states it. *)
Hypothesis HSTK : STK_LLVMF <= LLVMF_STK.
Hypothesis HEV : EV_LLVMF <= EV_LIB.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis MTL : ameter_laws MT.
Hypothesis MTF : ameter_fs_laws MT.
Hypothesis AFREE4 : afree04_rule SEGS B MT.
Hypothesis ASF : astack_free_law SEGS B.
Hypothesis FFL : frame_flag_lawP SEGS B.
Hypothesis ASSF5 : aset_shadow_realizes SEGS B (SIGMA IB___asan_set_shadow_f5) 0xf5.
Hypothesis HXN : forall n, EV_LLVMF * (mo_malloc MT 256 + mo_free MT) <= XN_LIB n.
(* The contract's HUMF, with LLVMF_FREE_CTX unfolded. *)
Hypothesis HUMF : forall c,
In c (map (fun o => [BASE + o; RA_LLVMF]) LLVMF_FREE_RAS ++ map (fun o => [BASE + o]) LLVMF_FREE_RAS) ->
In (firstn kUnwindMax (pc_free_ra0 (as_code B)
:: flat_map (fun r => if r =? pc_free_ra0 (as_code B) then [] else [r]) c)) (as_universe B).
(* cgif ACfh.v:29-31 *)
Hypothesis AJ_FP_NIL : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k.
(* cgif ACfh.v:162-164 *)
Hypothesis AJ_NIL_IO : forall STK sp0 ly S (W : world SEGS) mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 [] ly S W mem md own ly' S' W' mem' md' k ->
m_fds md' = m_fds md /\ m_fs md' = m_fs md.
(* the two kept-lemmas of identity's relocated YE01 *)
Hypothesis ASINK_NONE_KEPT : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
~ YI16.sink_open_fp FP ->
asink_none SEGS KS (rd W mem) md -> asink_none SEGS KS (rd W' mem') md'.
Hypothesis AMETA_INV_KEPT : forall STK sp0 FP ly S W mem md own ly' S' W' mem' md' k M,
ajournal SEGS B STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
ameta_inv SEGS KS ly (rd W mem) M -> ameta_inv SEGS KS ly' (rd W' mem') M.
Let RUNP := SRr_run_pi_AJ B LAWS.
Let RUNC := SRr_run_pi_AJ_call B LAWS.
Let RUNF := aj_flag_store_pi B LAWS ML ASF FFL.
Let RET := paj_ret_at (PL := PL_identb) (PI := PI).

(* ---- small helpers ----------------------------------------------------------------------------- *)
Lemma l_pres : forall (r : bv 5) (regs regs' : bvmap 5 word),
aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) -> getr regs' r = getr regs r.
Proof.
intros r regs regs' H Hr. specialize (H (bv_unsigned r) Hr). rewrite Z_to_bv_bv_unsigned in H. exact H.
Qed.

(* A block the run allocated is not one of the entry's: two equal blocks in one state would have to
   be separated from each other, which no block of positive request size is. *)
Lemma l_fresh : forall ly3 S3 (W3 : world SEGS) mem3 md3 p n l,
AR SEGS B ly3 S3 W3 mem3 md3 -> Permutation (ablocks B ly3 S3) ((p, n) :: l) -> 0 <= n ->
In (p, n) l -> False.
Proof.
intros ly3 S3 W3 mem3 md3 p n l HAR Hperm Hn Hin.
apply in_split in Hin as (l1 & l2 & ->).
assert (Hp2 : Permutation (ablocks B ly3 S3) ((p, n) :: (p, n) :: (l1 ++ l2))).
{ eapply Permutation_trans; [exact Hperm|]. apply perm_skip. apply Permutation_sym, Permutation_middle. }
pose proof (sep_blocks_perm SEGS B LAWS ly3 S3 W3 mem3 md3 (p, n) (p, n) (l1 ++ l2) HAR Hp2) as Hd.
unfold zdisjoint, block_rng in Hd. cbn [fst snd] in Hd.
pose proof (req_size_pos n Hn) as Hq. lia.
Qed.

(* The contract's pre-condition at the entry state, with the Section arguments _inv.v discharges
   e_pre over. *)
Definition l_pre (g : ectx) : Prop :=
e_pre B MT XM_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS g.

(* The call chain at a call made from the entry's own frame: either empty (the entry's frame pointer
   is within 16 bytes of the layout's top) or the entry's single frame record. *)
Lemma l_chain : forall (g : ectx) (pos mf : Z) ly3 S3 (W3 : world SEGS) memT md3 k (regsT : bvmap 5 word),
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly3 S3 W3 memT md3 k ->
l_pre g ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
spZ regsT = mf -> s0Z regsT = e_sp0 g -> 4096 <= raZ regsT ->
val_mem SEGS (rd W3 memT) (e_sp0 g - 8) 8 RA_LLVMF ->
val_mem SEGS (rd W3 memT) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
exists ch, chain_pre ly3 (aview SEGS (w_H W3) memT) regsT ch /\
(ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]).
Proof.
intros g pos mf ly3 S3 W3 memT md3 k regsT HJ HPRE Hmfb Usp Us0 Ura4 Vra Vs0.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Has : ASTACK = 16384) by reflexivity.
pose proof HPRE as (HFN & Hraz & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HFN as (HAR0 & _ & Hra4 & _ & _ & _ & _ & Hch0 & _).
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & _ & _ & _ & F1 & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & _ & _ & _ & ETop & _).
assert (Htop64 : ly_top ly3 <= 2 ^ 64) by (rewrite ETop; clear - Htop1 Hshi H47; lia).
assert (Hach : achain ly3 (aview SEGS (w_H (e_W g)) (e_mem g)) (e_sp0 g) (s0Z (e_regs g)) []).
{ apply (achain_ly_top (e_ly g)); [exact ETop | exact Hch0]. }
destruct (Z.lt_ge_cases (e_sp0 g) (ly_top ly3 - 16)) as [Hlt | Hge].
- exists [(e_sp0 g, RA_LLVMF, s0Z (e_regs g))].
  split; [|right; exists (e_sp0 g), (s0Z (e_regs g)); reflexivity].
  eapply (achain_chain_pre ly3 _ mf (e_sp0 g));
  [| rewrite Usp; clear - Hmfb Hceil Hslo HSTK' Has; lia | exact Us0 | exact Ura4].
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 1)) as Rra.
  change (bv_modulus 64) with (2 ^ 64) in Rra.
  pose proof (bv_unsigned_in_range 64 (getr (e_regs g) 8)) as Rs0r.
  change (bv_modulus 64) with (2 ^ 64) in Rs0r.
  apply (achain_push ly3 _ _ (e_sp0 g) (s0Z (e_regs g)) RA_LLVMF [] mf Hach).
  + exact Htop64.
  + intros a Ha. apply F1; clear - Ha Hceil Hslo HSTK' Has C1; lia.
  + apply rdword_of_val_mem; [exact Vra | unfold raZ in Hraz; clear - Hraz Rra; lia].
  + apply rdword_of_val_mem; [exact Vs0 | unfold s0Z; clear - Rs0r; lia].
  + rewrite <- Hraz. exact Hra4.
  + clear - Hceil Hslo HSTK' Has. lia.
  + clear - Hsp0al. lia.
  + exact Hlt.
  + clear - Hmfb. lia.
- exists []. split; [|left; reflexivity].
  eapply (achain_chain_pre ly3 _ mf (e_sp0 g) []);
  [| rewrite Usp; clear - Hmfb Hceil Hslo HSTK' Has; lia | exact Us0 | exact Ura4].
  left. split; [right; left; clear - Hge; lia | reflexivity].
Qed.

(* The allocator-universe premise of a free call of this segment, in both chain shapes
   (_inv.v's llvmf_univ_call / llvmf_univ_call0). *)
Lemma l_univ : forall (regsT : bvmap 5 word) ch o,
In o l_FREE_OFFS -> raZ regsT = BASE + o ->
(ch = [] \/ exists fp v, ch = [(fp, RA_LLVMF, v)]) ->
In (call_trace0 (pc_free_ra0 (as_code B)) regsT ch) (as_universe B).
Proof.
assert (HOFF : forall o, In o l_FREE_OFFS -> In o LLVMF_FREE_RAS)
by (intros o Ho; unfold l_FREE_OFFS in Ho; unfold LLVMF_FREE_RAS; cbn [In] in Ho |- *; tauto).
intros regsT ch o Ho Hra [-> | (fp & v & ->)].
- eapply llvmf_univ_call0; [exact HUMF|].
  apply in_or_app. right. apply in_map_iff. exists o.
  split; [rewrite Hra; reflexivity | exact (HOFF o Ho)].
- eapply llvmf_univ_call; [exact HUMF|].
  apply in_or_app. left. apply in_map_iff. exists o.
  split; [rewrite Hra; reflexivity | exact (HOFF o Ho)].
Qed.

(* ---- one free call ------------------------------------------------------------------------------ *)
Lemma l_free_one : forall (g : ectx) (pos mf : Z) ly3 S3 (W3 : world SEGS) (regsT : bvmap 5 word)
(memT : word -> option byte) md3 k o pa n,
l_pre g ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly3 S3 W3 memT md3 k ->
frames S3 = [(4, pos)] ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
getr regsT 2 = w64 mf -> getr regsT 8 = w64 (e_sp0 g) ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = Z_to_bv 64 (BASE + o) -> In o l_FREE_OFFS ->
getr regsT 10 = w64 pa ->
In (pa, n) (ablocks B ly3 S3) -> ~ In (pa, n) (ablocks B (e_ly g) (e_S g)) -> 0 <= n ->
val_mem SEGS (rd W3 memT) (e_sp0 g - 8) 8 RA_LLVMF ->
val_mem SEGS (rd W3 memT) (e_sp0 g - 16) 8 (s0Z (e_regs g)) ->
0 <= k < EV_LLVMF -> mo_ok MT S3 (mo_free MT) ->
SRr SEGS W3 (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) md3)
(fun W4 c4 => exists ly4 S4 regs4 mem4 md4,
c4 = mkCfg (mkst regs4 (Z_to_bv 64 (BASE + o)) mem4 (seg_rom SEGS)) md4 /\
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly4 S4 W4 mem4 md4 (k + 1) /\
aregs_preserved regsT regs4 /\
(exists l1 l2, ablocks B ly3 S3 = l1 ++ (pa, n) :: l2 /\ ablocks B ly4 S4 = l1 ++ l2) /\
frames S4 = frames S3 /\
mo_le MT S3 S4 (mo_free MT) /\
(forall a, SFa g pos + 8 <= a < SFa g pos + 1024 ->
aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) memT a) /\
(forall a, mf <= a < e_sp0 g -> aview SEGS (w_H W4) mem4 a = aview SEGS (w_H W3) memT a)).
Proof.
intros g pos mf ly3 S3 W3 regsT memT md3 k o pa n HPRE HJ Hfrs3 Hmfb Hmf32 Rsp Rs0 Rgp Rtp Rra Ho
Ra0 Hin3 HnotE Hn0 Vra Vs0 Hk MOKf.
pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
assert (Hoff : 0 <= o < 2 ^ 40 /\ o mod 2 = 0)
by (unfold l_FREE_OFFS in Ho; cbn [In] in Ho;
    destruct Ho as [<- | [<- | [<- | []]]]; (split; [lia | reflexivity])).
pose proof HPRE as (HFN & Hraz & _ & _ & _ & _ & _ & Hfrs0 & Hnev0 & _ & _ & _ & _ & _ & _ & _).
pose proof HJ as (HAR3 & Hly3 & _ & _ & _ & Hfrs3j & Hnev3 & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & _ & Htop0 & Htop1).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 memT md3 4 pos HAR3 Hin4) as (HSF0 & HSF1 & HSFapp).
rewrite EFa in HSF0, HSF1, HSFapp. rewrite HFB in HSF1, HSFapp.
assert (Usp : spZ regsT = mf)
by (unfold spZ; rewrite Rsp; unfold w64; apply unsigned_lit_small;
    clear - Hmfb Hceil Hslo HSTK' Has H47 Hshi C1; lia).
assert (Us0 : s0Z regsT = e_sp0 g)
by (unfold s0Z; rewrite Rs0; unfold w64; apply unsigned_lit_small;
    clear - Hceil Hslo HSTK' Has H47 Hshi C1; lia).
assert (Ura : raZ regsT = BASE + o)
by (unfold raZ; rewrite Rra; apply unsigned_lit_small; clear - HBASE Hoff; lia).
assert (Hnev : st_nev S3 < EV_MAX) by (clear - Hnev3 Hnev0 Hk HEV; unfold EV_LLVMF in *; lia).
destruct (l_chain g pos mf ly3 S3 W3 memT md3 k regsT HJ HPRE Hmfb Usp Us0
ltac:(rewrite Ura; clear - HBLO Hoff; lia) Vra Vs0) as (ch & Hchain & Hchs).
eapply SRr_mono.
{ eapply (afree04_sub SEGS B LAWS pa_segs_low MT AFREE4 W3 regsT memT LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)] ly3 S3 md3 k pa n (mf - e_sp0 g)
    (Z_to_bv 64 (BASE + o)) ch HJ Hin3).
  - exact Ra0.
  - rewrite Usp. clear. lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - clear - Hmfb HSTK' Has. lia.
  - exact Rgp.
  - exact Rtp.
  - exact Rra.
  - apply ret_ok_codeptr_v; [clear - Hoff; lia | exact (proj2 Hoff)].
  - exact Hnev.
  - exact Hchain.
  - exact (l_univ regsT ch o Ho Ura Hchs).
  - intros Hin. exfalso. exact (HnotE Hin).
  - exact MOKf. }
cbv beta. intros W4 c4 _ (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 & Hbl4 & Hfrs4 & HK4 & MLE4 & _).
exists ly4, S4, regs4, mem4, md4. split; [reflexivity|].
split; [exact HJ4|]. split; [exact HP4|]. split; [exact Hbl4|]. split; [exact Hfrs4|].
split; [exact MLE4|].
pose proof HK4 as (K1 & K2 & K3 & K4 & K5 & K6).
destruct (al_blocks _ _ LAWS ly3 S3 W3 memT md3 pa n HAR3 Hin3) as (_ & Hpa0 & Hpace & Hpaapp & _).
pose proof (sep_block_frame SEGS B LAWS ly3 S3 W3 memT md3 pa n 4 pos HAR3 Hin3 Hin4) as Hdf.
unfold zdisjoint in Hdf. cbn [fst snd] in Hdf. rewrite EFa, HFB in Hdf.
split.
- intros a Ha. rewrite (K4 4 pos a Hin4).
  + reflexivity.
  + unfold in_zr, frame_rng. cbn [fst snd]. rewrite EFa, HFB. left. clear - Ha. lia.
  + cbn beta. intros Hp. clear - Ha Hp Hdf. lia.
- intros a Ha. apply K1; clear - Ha Hmfb Hceil Hslo HSTK' Has H47 Hshi C1; lia.
Qed.

(* ---- the shadow fill of the frame release ------------------------------------------------------- *)
Lemma l_shadow : forall (g : ectx) (pos mf : Z) ly3 S3 (W3 : world SEGS) (regsT : bvmap 5 word)
(memT : word -> option byte) md3 k,
l_pre g ->
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly3 S3 W3 memT md3 k ->
frames S3 = [(4, pos)] ->
e_sp0 g - 336 <= mf <= e_sp0 g - 320 -> mf mod 32 = 0 ->
getr regsT 2 = w64 mf ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) -> YK0s.ret_ok (getr regsT 1) ->
getr regsT 10 = w64 (shadow_addr (SFa g pos)) -> getr regsT 11 = w64 128 ->
SRr SEGS W3
(mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___asan_set_shadow_f5)) memT (seg_rom SEGS)) md3)
(fun W4 c4 => W4 = W3 /\ exists regs4 mem4 md4,
c4 = mkCfg (mkst regs4 (Z_to_bv 64 (raZ regsT)) mem4 (seg_rom SEGS)) md4 /\
ajournal SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [(4, pos)]
ly3 S3 W3 mem4 md4 k /\
aregs_preserved regsT regs4 /\
(forall a, 0 <= a < 2 ^ 64 ->
~ (shadow_addr (SFa g pos) <= a < shadow_addr (SFa g pos) + 128) ->
aview SEGS (w_H W3) mem4 a = aview SEGS (w_H W3) memT a)).
Proof.
intros g pos mf ly3 S3 W3 regsT memT md3 k HPRE HJ Hfrs3 Hmfb Hmf32 Rsp Rgp Rtp Rraok Ra0 Ra1.
pose proof pa_segs_low as Hsegs.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (_ & _ & _ & _ & _ & _ & _ & Hfrs0 & _ & _ & _ & _ & _ & _ & _ & _).
pose proof HJ as (HAR3 & Hly3 & Hsecs & Hwle & Hio & Hfrs3j & Hnev3 & Hk0 &
F1 & F2 & F3 & F4 & Hgone & Hpres & Hstatic & F5 & HQT).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop1).
pose proof Hly3 as (_ & _ & _ & _ & _ & EF & _ & _ & _ & _ & _ & _ & _ & Eextra & _).
assert (EFa : frame_addr ly3 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S3)) by (rewrite Hfrs3; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly3 S3 W3 memT md3 4 pos HAR3 Hin4) as (HSF0 & HSF1 & HSFapp).
rewrite EFa in HSF0, HSF1, HSFapp. rewrite HFB in HSF1, HSFapp.
assert (Esh : shadow_addr (SFa g pos) = 2147450880 + SFa g pos / 8) by reflexivity.
pose proof (shadow_addr_bounds (SFa g pos) ltac:(clear - HSF0 HSF1 C1 C4; lia)) as Hshb.
assert (Hshlo : 2147450880 <= shadow_addr (SFa g pos))
by (clear - Hshb C5; unfold kLowMemEnd in *; lia).
assert (Hshhi : shadow_addr (SFa g pos) + 128 < alloc_ceiling)
by (clear - Hshb C1 C2; unfold kHighShadowEnd in *; lia).
assert (HPRECALL : ecall_pre SEGS B ly3 S3 W3 regsT memT md3).
{ eapply (ecall_pre_at SEGS B LLVMF_STK (e_sp0 g) [] (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g)
    [(4, pos)] ly3 S3 W3 memT md3 k regsT (mf - e_sp0 g) HJ).
  - unfold spZ. rewrite Rsp. unfold w64. rewrite unsigned_lit_small by
      (clear - Hmfb Hceil Hslo HSTK' Has H47 Hshi C1; lia). clear. lia.
  - clear - Hmf32 Hsp0al. lia.
  - clear - Hmfb. lia.
  - clear - Hmfb HSTK' Has Hes. lia.
  - exact Rraok.
  - exact Rgp.
  - exact Rtp. }
replace (mkCfg (mkst regsT (Z_to_bv 64 (SIGMA IB___asan_set_shadow_f5)) memT (seg_rom SEGS)) md3)
with (cfg_at SEGS (SIGMA IB___asan_set_shadow_f5) regsT memT md3) by reflexivity.
eapply SRr_mono.
{ exact (ASSF5 ly3 S3 W3 regsT memT md3 4 pos (shadow_addr (SFa g pos)) 128 HPRECALL Hin4 Ra0 Ra1
    ltac:(lia) ltac:(rewrite EFa; lia) ltac:(rewrite EFa, HFB; lia)). }
cbv beta. intros W4 c4 _ (-> & regs4 & mem4 & md4 & -> & HAR4 & HP4 & Hsame & Hfill & Hkeep & Hpres4).
split; [reflexivity|]. exists regs4, mem4, md4. split; [reflexivity|].
split; [| split; [exact HP4 | exact Hkeep]].
split; [exact HAR4|].
split; [exact Hly3|]. split; [exact Hsecs|]. split; [exact Hwle|].
split; [eapply aos_step_same_io; [exact Hio | apply same_io_materialized, Hsame]|].
split; [exact Hfrs3j|]. split; [exact Hnev3|]. split; [exact Hk0|].
split.
{ intros a Ha Hs. rewrite Hkeep by (clear - Ha Hshhi C1; lia). exact (F1 a Ha Hs). }
split.
{ intros p n i H1 H2 Hi Hnf.
  destruct (al_blocks _ _ LAWS ly3 S3 W3 memT md3 p n HAR3 H2) as (_ & Hp0 & Hpce & Hpapp & _).
  rewrite Hkeep.
  - exact (F2 p n i H1 H2 Hi Hnf).
  - clear - Hi Hp0 Hpce C1. lia.
  - intros Hw. apply (fshadow_not_app (SFa g pos) 128 p (req_size n) (p + i));
    [ clear - HSF0; lia | clear - HSF1 C1 C4; lia | exact Hpapp
    | rewrite <- Esh; exact Hw | clear - Hi; lia ]. }
split.
{ intros a Hi Hns He Hsp. pose proof (Hsegs a Hi) as Hal'.
  rewrite Hkeep by (clear - Hal' Hshlo C5; unfold kLowMemEnd in *; lia).
  exact (F3 a Hi Hns He Hsp). }
split.
{ intros cid pos' a Hin Hr Hnf. rewrite Hfrs0 in Hin. destruct Hin. }
split; [exact Hgone|].
split.
{ intros a Ha. eapply (apresent_transfer SEGS (w_H W3) (w_H W3) memT mem4 a).
  - clear - Ha Hceil Hslo HSTK' Has H47 Hshi C1. lia.
  - intros Him. pose proof (Hsegs a Him) as Hlow.
    clear - Hlow Ha Hceil Hslo HSTK' Has C1 C5. unfold kLowMemEnd in *. lia.
  - apply Hkeep; [clear - Ha Hceil Hslo HSTK' Has H47 Hshi C1; lia
                 | clear - Ha Hceil Hslo HSTK' Has Hshhi C1; lia].
  - exact (Hpres a Ha). }
split; [exact Hstatic|].
split; [|exact HQT].
{ intros a HXa He.
  assert (HXc : Exists (in_zr a) (ly_extra ly3)) by (rewrite Eextra; exact HXa).
  pose proof (AR_extra_law_ok SEGS B ly3 S3 W3 memT md3 a HAR3 HXc)
    as (Xo & Xb & Xf & Xs & Xi & Xsh & Xapp).
  assert (Ha64 : 0 <= a < 2 ^ 64)
    by (unfold app_addr, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in Xapp; clear - Xapp C1; lia).
  rewrite Hkeep.
  - exact (F5 a HXa He).
  - exact Ha64.
  - intros Hw. apply (proj2 (Xf 4 pos Hin4)). unfold in_zr. cbn [fst snd].
    rewrite EFa, HFB. clear - Hw. lia. }
Qed.

(* ---- the live memory this segment carries ------------------------------------------------------- *)
Definition l_live (g : ectx) (pos mf nm dp : Z) (W2 : world SEGS) (mem2 : word -> option byte) : Prop :=
val_mem SEGS (rd W2 mem2) (mf + 16) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (mf + 64) 8 (SFa g pos) /\
val_mem SEGS (rd W2 mem2) (mf + 152) 8 nm /\
val_mem SEGS (rd W2 mem2) (mf + 184) 8 dp /\
val_mem SEGS (rd W2 mem2) (SFa g pos + 1016) 8 (flag_addr (e_ly g) 4 pos) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 8) 8 RA_LLVMF /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 16) 8 (s0Z (e_regs g)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 24) 8 (bv_unsigned (getr (e_regs g) 9)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 32) 8 (bv_unsigned (getr (e_regs g) 18)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 40) 8 (bv_unsigned (getr (e_regs g) 19)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 48) 8 (bv_unsigned (getr (e_regs g) 20)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 56) 8 (bv_unsigned (getr (e_regs g) 21)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 64) 8 (bv_unsigned (getr (e_regs g) 22)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 72) 8 (bv_unsigned (getr (e_regs g) 23)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 80) 8 (bv_unsigned (getr (e_regs g) 24)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 88) 8 (bv_unsigned (getr (e_regs g) 25)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 96) 8 (bv_unsigned (getr (e_regs g) 26)) /\
val_mem SEGS (rd W2 mem2) (e_sp0 g - 104) 8 (bv_unsigned (getr (e_regs g) 27)).

Lemma l_live_keep : forall (g : ectx) (pos mf nm dp : Z) (W W' : world SEGS) m m',
e_sp0 g - 336 <= mf <= e_sp0 g - 320 ->
(forall a, SFa g pos + 8 <= a < SFa g pos + 1024 ->
aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
(forall a, mf <= a < e_sp0 g -> aview SEGS (w_H W') m' a = aview SEGS (w_H W) m a) ->
l_live g pos mf nm dp W m -> l_live g pos mf nm dp W' m'.
Proof.
intros g pos mf nm dp W W' m m' Hmfb KF KSt
(A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 & A18).
unfold l_live.
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (mf + 16) (mf + 16) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A1]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (mf + 64) (mf + 64) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A2]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (mf + 152) (mf + 152) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A3]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (mf + 184) (mf + 184) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A4]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (SFa g pos + 1016) (SFa g pos + 1016) 8);
  [intros kk Hkk; apply KF; clear - Hkk; lia | exact A5]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 8) (e_sp0 g - 8) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A6]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 16) (e_sp0 g - 16) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A7]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 24) (e_sp0 g - 24) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A8]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 32) (e_sp0 g - 32) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A9]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 40) (e_sp0 g - 40) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A10]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 48) (e_sp0 g - 48) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A11]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 56) (e_sp0 g - 56) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A12]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 64) (e_sp0 g - 64) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A13]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 72) (e_sp0 g - 72) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A14]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 80) (e_sp0 g - 80) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A15]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 88) (e_sp0 g - 88) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A16]|].
split; [eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 96) (e_sp0 g - 96) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A17]|].
eapply (val_mem_moved SEGS (w_H W) (w_H W') m m' (e_sp0 g - 104) (e_sp0 g - 104) 8);
  [intros kk Hkk; apply KSt; clear - Hkk Hmfb; lia | exact A18].
Qed.

(* ---- the segment -------------------------------------------------------------------------------- *)
Theorem seg_L_holds : seg_L_stmt B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB
LIVE_LIB asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof.
intros g pos mf nm tk dp W2 c2 Hstart.
destruct Hstart as (ly2 & S2 & regs2 & mem2 & md2 & -> & HJ & Hfrs & Hk & MLE & MOK & HC & HP).
destruct HC as (Rsp & Rs1 & Rs0 & Hmfb & Hmf32 & Rgp & Rtp & M16 & M64 & M192 & M168 &
Vra & Vs0 & V24 & V32 & V40 & V48 & V56 & V64 & V72 & V80 & V88 & V96 & V104 & Vflag &
HPRE & Hfds & Hfsm & Hinb).
destruct HP as (Hbl & Rs7 & Rs5 & M152 & M184).
unfold MEV in MLE, MOK.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs.
pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (Has : ASTACK = 16384) by reflexivity.
assert (Hes : ESTACK = 4096) by reflexivity.
assert (HFB : fs_frame_bytes 4 = 1024) by reflexivity.
pose proof HSTK as HSTK'. unfold STK_LLVMF in HSTK'.
pose proof HPRE as (HFN & Hraz & Ha0e & Ha1e & Hinp & Hlen & Hgarr & Hfrs0 & Hnev0 & Hlive0 &
Hro0 & Hsnk0 & Hfd0 & Hsort0 & Hmeta0 & Hmo0).
pose proof HFN as (HAR0 & Hraok0 & Hra4 & Hgp0 & Htp0 & Hstk00 & Hpres0 & Hch0 & HQT0).
unfold YK0s.ret_ok in Hraok0.
unfold raZ in Hraz.
pose proof HJ as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & Hnev2 & _ & _ & _ & _ & _ & _ & _ & Hstatic & _).
pose proof Hstatic as (Hsp0al & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop0 & Htop1).
pose proof Hly2 as (_ & _ & _ & _ & _ & EF & _).
assert (EFa2 : frame_addr ly2 4 pos = SFa g pos) by (unfold SFa, frame_addr; rewrite EF; reflexivity).
assert (Hin4 : In (4, pos) (frames S2)) by (rewrite Hfrs; left; reflexivity).
destruct (frames_bounds SEGS B LAWS ly2 S2 W2 mem2 md2 4 pos HAR2 Hin4) as (HSF0 & HSF1 & HSFapp).
rewrite EFa2 in HSF0, HSF1, HSFapp. rewrite HFB in HSF1, HSFapp.
assert (Hmf0 : alloc_ceiling + 16384 <= mf) by (clear - Hmfb Hceil Hslo HSTK' Has; lia).
assert (Esh : shadow_addr (SFa g pos) = 2147450880 + SFa g pos / 8) by reflexivity.
pose proof (shadow_addr_bounds (SFa g pos) ltac:(clear - HSF0 HSF1 C1 C4; lia)) as Hshb.
assert (Hshlo : 2147450880 <= shadow_addr (SFa g pos))
by (clear - Hshb C5; unfold kLowMemEnd in *; lia).
assert (Hshhi : shadow_addr (SFa g pos) + 128 < alloc_ceiling)
by (clear - Hshb C1 C2; unfold kHighShadowEnd in *; lia).
(* the frame and its own shadow do not meet *)
assert (HSFsh : shadow_addr (SFa g pos) + 128 <= SFa g pos \/
                SFa g pos + 1024 <= shadow_addr (SFa g pos)).
{ destruct (Z.le_gt_cases (shadow_addr (SFa g pos) + 128) (SFa g pos)) as [H1|H1]; [left; exact H1|].
  destruct (Z.le_gt_cases (SFa g pos + 1024) (shadow_addr (SFa g pos))) as [H2|H2]; [right; exact H2|].
  exfalso.
  apply (fshadow_not_app (SFa g pos) 128 (SFa g pos) 1024
    (Z.max (shadow_addr (SFa g pos)) (SFa g pos)));
  [ clear - HSF0; lia | clear - HSF1 C1 C4; lia | exact HSFapp
  | rewrite <- Esh; clear - H1 H2; lia | clear - H1 H2; lia ]. }
(* the event count and the meter *)
set (nrec := m_nrec g) in *.
assert (Hnrec : (nrec <= 64)%nat) by (clear - Hk; unfold EV_LLVMF in Hk; lia).
pose proof (mo_malloc_nonneg MT MTL 256 ltac:(lia)) as HM0.
pose proof (mo_free_nonneg MT MTL) as HF0.
assert (HT3 : 3 * mo_free MT <=
  (EV_LLVMF - (4 * Z.of_nat nrec + 7)) * (mo_malloc MT 256 + mo_free MT))
by (unfold EV_LLVMF; clear - HM0 HF0 Hnrec; nia).
(* the three heap blocks *)
set (Nn := Z.max (SlotModel.t_cap_name (e_pl g)) 1) in *.
set (Nt := Z.max (SlotModel.t_cap_tok (e_pl g)) 1) in *.
set (Nd := Z.max (SlotModel.t_cap_disp (e_pl g)) 1) in *.
destruct Hbl as (Hperm & Hpos).
assert (HNn : 0 <= Nn) by (unfold Nn; pose proof (Z.le_max_r (SlotModel.t_cap_name (e_pl g)) 1); lia).
assert (HNt : 0 <= Nt) by (unfold Nt; pose proof (Z.le_max_r (SlotModel.t_cap_tok (e_pl g)) 1); lia).
assert (HNd : 0 <= Nd) by (unfold Nd; pose proof (Z.le_max_r (SlotModel.t_cap_disp (e_pl g)) 1); lia).
assert (Hpermd : Permutation (ablocks B ly2 S2)
  ((dp, Nd) :: [(nm, Nn); (tk, Nt)] ++ ablocks B (e_ly g) (e_S g))).
{ eapply Permutation_trans; [exact Hperm|].
  apply Permutation_sym. apply (Permutation_middle [(nm, Nn); (tk, Nt)] _ (dp, Nd)). }
assert (Hind : In (dp, Nd) (ablocks B ly2 S2))
by (eapply Permutation_in; [apply Permutation_sym; exact Hpermd | left; reflexivity]).
assert (HnotEd : ~ In (dp, Nd) (ablocks B (e_ly g) (e_S g))).
{ intros Hx. apply (l_fresh ly2 S2 W2 mem2 md2 dp Nd _ HAR2 Hpermd HNd).
  apply in_or_app. right. exact Hx. }
assert (LIVE2 : l_live g pos mf nm dp W2 mem2)
by (unfold l_live; repeat split; assumption).
unfold cfg_at. change (w64 (BASE + 0x1bec)) with (Z_to_bv 64 (BASE + 0x1bec)).
(* ================ run 1: +0x1bec, the load of dp, and the free ================ *)
remember (Eimg (Ereg regs2 [Z_to_bv 64 dp])) as E1 eqn:HE1.
assert (HEI1 : img_env VAL A_LIM E1) by (rewrite HE1; apply Eimg_env).
assert (EE1 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E1 n = getr regs2 r)
by (intros n r Hn; rewrite HE1; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E1_32 : ew E1 32 = Z_to_bv 64 dp)
by (rewrite HE1, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs2 _ 0)).
assert (U1_9 : bv_unsigned (ew E1 9) = mf).
{ rewrite (EE1 9%nat 9%bv eq_refl), Rs1. unfold w64. apply unsigned_lit_small.
  clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Hdp64 : 0 <= dp < 2 ^ 64).
{ destruct (al_blocks _ _ LAWS ly2 S2 W2 mem2 md2 dp Nd HAR2 Hind) as (_ & Hd0 & Hdc & _).
  pose proof (req_size_pos Nd HNd) as Hq. clear - Hd0 Hdc Hq C1. lia. }
assert (HS1 : st_ok_pi SEGS VAL E1 l_ss1
  (restrict (w_H W2) (mkst regs2 (Z_to_bv 64 (BASE + 0x1bec)) mem2 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold l_ss1. apply pa_entry_st_ok_full.
  - rewrite HE1. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold l_r1mf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U1_9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi C1; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E1 _ mf 184 8 (SOff 32 0) dp);
    [ cbn [sv_denot]; rewrite E1_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - Hdp64; cbn; lia | cbn; lia | exact M184 ].
  - cbn [pairwise_disjoint all_disjoint].
    repeat match goal with |- _ /\ _ => split end; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_shc RUNP RUNC HS1 HJ.
{ intros a (r & Hr & Ha). unfold l_ss1 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. unfold l_r1mf in Ha.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
assert (KEEP1 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W2) (ms_mem ms) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha. apply (kept_of_frame E1 _ (w_H W2) mem2 (ms_mem ms) (fun _ => False) HFr);
  [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold l_ss1, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. cbn [base_val] in Hr. lia. }
clear HF HFr HG.
prreg HS1 (10%bv : bv 5) R1_10. prreg HS1 (1%bv : bv 5) R1_1. prreg HS1 (2%bv : bv 5) R1_2.
prreg HS1 (3%bv : bv 5) R1_3. prreg HS1 (4%bv : bv 5) R1_4. prreg HS1 (8%bv : bv 5) R1_8.
prreg HS1 (9%bv : bv 5) R1_9. prreg HS1 (21%bv : bv 5) R1_21. prreg HS1 (23%bv : bv 5) R1_23.
rewrite (EE1 2%nat 2%bv eq_refl), Rsp in R1_2. rewrite (EE1 3%nat 3%bv eq_refl), Rgp in R1_3.
rewrite (EE1 4%nat 4%bv eq_refl), Rtp in R1_4. rewrite (EE1 8%nat 8%bv eq_refl), Rs0 in R1_8.
rewrite (EE1 9%nat 9%bv eq_refl), Rs1 in R1_9. rewrite (EE1 21%nat 21%bv eq_refl), Rs5 in R1_21.
rewrite (EE1 23%nat 23%bv eq_refl), Rs7 in R1_23. rewrite E1_32 in R1_10.
assert (LIVE1 : l_live g pos mf nm dp W2 (ms_mem ms))
by (eapply l_live_keep; [exact Hmfb | intros a Ha; apply KEEP1; clear - Ha HSF0 HSF1 C1; lia
   | intros a Ha; apply KEEP1; clear - Ha Hmf0 Hmfb H47 Hshi C1; lia | exact LIVE2]).
destruct LIVE1 as (L1_16 & L1_64 & L1_152 & L1_184 & L1_fl & L1_ra & L1_s0 & L1_24 & L1_32 &
L1_40 & L1_48 & L1_56 & L1_64b & L1_72 & L1_80 & L1_88 & L1_96 & L1_104).
assert (MOK1 : mo_ok MT S2 (mo_free MT))
by (apply (mo_ok_le MT MTL S2 _ _ MOK); clear - HT3 HF0; lia).
pmkst HS1. rewrite (pal_free B TL).
eapply SRr_bind.
{ eapply (l_free_one g pos mf ly2 S2 W2 (ms_regs ms) (ms_mem ms) _ (4 * Z.of_nat nrec + 7)
    0x1bf4 dp Nd HPRE HJ Hfrs Hmfb Hmf32);
  [ exact R1_2 | exact R1_8 | exact R1_3 | exact R1_4 | exact R1_1
  | left; reflexivity | exact R1_10 | exact Hind | exact HnotEd | exact HNd
  | exact L1_ra | exact L1_s0 | clear - Hk; unfold EV_LLVMF in *; lia | exact MOK1 ]. }
cbv beta. intros W3 c3 Hwle3 (ly3 & S3 & regs3 & mem3 & md3 & -> & HJ3 & HP3 &
(dl1 & dl2 & Edb & Edb3) & Hfrs3 & MLE3 & KF3 & KS3).
assert (Hfrs3' : frames S3 = [(4, pos)]) by (rewrite Hfrs3; exact Hfrs).
assert (LIVE3 : l_live g pos mf nm dp W3 mem3)
by (eapply l_live_keep; [exact Hmfb | exact KF3 | exact KS3
   | unfold l_live; repeat split; assumption]).
assert (Hperm3 : Permutation (ablocks B ly3 S3)
  ([(nm, Nn); (tk, Nt)] ++ ablocks B (e_ly g) (e_S g))).
{ rewrite Edb3. rewrite Edb in Hpermd.
  apply (Permutation_cons_inv (a := (dp, Nd))).
  eapply Permutation_trans; [apply Permutation_middle | exact Hpermd]. }
assert (R2p : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs3 r = getr (ms_regs ms) r)
by (intros r Hr; exact (l_pres r _ _ HP3 Hr)).
(* ================ run 2: +0x1bf4, `mv a0,s5`, and the free of tk ================ *)
remember (Eimg (Ereg regs3 [])) as E2' eqn:HE2.
assert (HEI2 : img_env VAL A_LIM E2') by (rewrite HE2; apply Eimg_env).
assert (EE2 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E2' n = getr regs3 r)
by (intros n r Hn; rewrite HE2; apply ew_Eimg_Ereg_nat; exact Hn).
assert (HS2 : st_ok_pi SEGS VAL E2' l_ss2
  (restrict (w_H W3) (mkst regs3 (Z_to_bv 64 (BASE + 0x1bf4)) mem3 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold l_ss2. apply pa_entry_st_ok_full.
  - rewrite HE2. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor.
  - cbn [pairwise_disjoint]. exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_shc RUNP RUNC HS2 HJ3.
{ apply awr_ok_nil. }
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W3) (ms_mem ms0) a = aview SEGS (w_H W3) mem3 a).
{ intros a Ha. apply (kept_of_frame E2' _ (w_H W3) mem3 (ms_mem ms0) (fun _ => False) HFr);
  [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold l_ss2, windows in Hin. cbn in Hin. destruct Hin. }
clear HF HFr HG.
prreg HS2 (10%bv : bv 5) R2_10. prreg HS2 (1%bv : bv 5) R2_1. prreg HS2 (2%bv : bv 5) R2_2.
prreg HS2 (3%bv : bv 5) R2_3. prreg HS2 (4%bv : bv 5) R2_4. prreg HS2 (8%bv : bv 5) R2_8.
prreg HS2 (9%bv : bv 5) R2_9. prreg HS2 (23%bv : bv 5) R2_23.
rewrite (EE2 21%nat 21%bv eq_refl), (R2p 21%bv ltac:(l_cs)), R1_21 in R2_10.
rewrite (EE2 2%nat 2%bv eq_refl), (R2p 2%bv ltac:(l_cs)), R1_2 in R2_2.
rewrite (EE2 3%nat 3%bv eq_refl), (R2p 3%bv ltac:(l_cs)), R1_3 in R2_3.
rewrite (EE2 4%nat 4%bv eq_refl), (R2p 4%bv ltac:(l_cs)), R1_4 in R2_4.
rewrite (EE2 8%nat 8%bv eq_refl), (R2p 8%bv ltac:(l_cs)), R1_8 in R2_8.
rewrite (EE2 9%nat 9%bv eq_refl), (R2p 9%bv ltac:(l_cs)), R1_9 in R2_9.
rewrite (EE2 23%nat 23%bv eq_refl), (R2p 23%bv ltac:(l_cs)), R1_23 in R2_23.
assert (LIVE2' : l_live g pos mf nm dp W3 (ms_mem ms0))
by (eapply l_live_keep; [exact Hmfb | intros a Ha; apply KEEP2; clear - Ha HSF0 HSF1 C1; lia
   | intros a Ha; apply KEEP2; clear - Ha Hmf0 Hmfb H47 Hshi C1; lia | exact LIVE3]).
destruct LIVE2' as (L2_16 & L2_64 & L2_152 & L2_184 & L2_fl & L2_ra & L2_s0 & L2_24 & L2_32 &
L2_40 & L2_48 & L2_56 & L2_64b & L2_72 & L2_80 & L2_88 & L2_96 & L2_104).
assert (Hint : In (tk, Nt) (ablocks B ly3 S3))
by (eapply Permutation_in; [apply Permutation_sym; exact Hperm3 | right; left; reflexivity]).
assert (Hpermt : Permutation (ablocks B ly3 S3)
  ((tk, Nt) :: [(nm, Nn)] ++ ablocks B (e_ly g) (e_S g))).
{ eapply Permutation_trans; [exact Hperm3|].
  apply Permutation_sym. apply (Permutation_middle [(nm, Nn)] _ (tk, Nt)). }
assert (HnotEt : ~ In (tk, Nt) (ablocks B (e_ly g) (e_S g))).
{ intros Hx. apply (l_fresh ly3 S3 W3 _ _ tk Nt _ (proj1 HJ3) Hpermt HNt).
  apply in_or_app. right. exact Hx. }
assert (MOK2 : mo_ok MT S3 (mo_free MT)).
{ apply (mok_station MT S2 S3 _ (mo_free MT) (mo_free MT) MTL MOK MLE3 HF0).
  clear - HT3 HF0. lia. }
pmkst HS2. rewrite (pal_free B TL).
eapply SRr_bind.
{ eapply (l_free_one g pos mf ly3 S3 W3 (ms_regs ms0) (ms_mem ms0) _ (4 * Z.of_nat nrec + 7 + 1)
    0x1bfc tk Nt HPRE HJ3 Hfrs3' Hmfb Hmf32);
  [ exact R2_2 | exact R2_8 | exact R2_3 | exact R2_4 | exact R2_1
  | right; left; reflexivity | exact R2_10 | exact Hint | exact HnotEt | exact HNt
  | exact L2_ra | exact L2_s0 | clear - Hk; unfold EV_LLVMF in *; lia | exact MOK2 ]. }
cbv beta. intros W4 c4 Hwle4 (ly4 & S4 & regs4 & mem4 & md4 & -> & HJ4 & HP4 &
(tl1 & tl2 & Etb & Etb4) & Hfrs4 & MLE4 & KF4 & KS4).
assert (Hfrs4' : frames S4 = [(4, pos)]) by (rewrite Hfrs4; exact Hfrs3').
assert (LIVE4 : l_live g pos mf nm dp W4 mem4)
by (eapply l_live_keep; [exact Hmfb | exact KF4 | exact KS4
   | unfold l_live; repeat split; assumption]).
assert (Hperm4 : Permutation (ablocks B ly4 S4) ([(nm, Nn)] ++ ablocks B (e_ly g) (e_S g))).
{ rewrite Etb4. rewrite Etb in Hpermt.
  apply (Permutation_cons_inv (a := (tk, Nt))).
  eapply Permutation_trans; [apply Permutation_middle | exact Hpermt]. }
assert (R3p : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs4 r = getr (ms_regs ms0) r)
by (intros r Hr; exact (l_pres r _ _ HP4 Hr)).
(* ================ run 3: +0x1bfc, the load of nm, and the free ================ *)
remember (Eimg (Ereg regs4 [Z_to_bv 64 nm])) as E3' eqn:HE3.
assert (HEI3 : img_env VAL A_LIM E3') by (rewrite HE3; apply Eimg_env).
assert (EE3 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E3' n = getr regs4 r)
by (intros n r Hn; rewrite HE3; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E3_32 : ew E3' 32 = Z_to_bv 64 nm)
by (rewrite HE3, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs4 _ 0)).
assert (U3_9 : bv_unsigned (ew E3' 9) = mf).
{ rewrite (EE3 9%nat 9%bv eq_refl), (R3p 9%bv ltac:(l_cs)), R2_9. unfold w64.
  apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (Hinn : In (nm, Nn) (ablocks B ly4 S4))
by (eapply Permutation_in; [apply Permutation_sym; exact Hperm4 | left; reflexivity]).
assert (Hnm64 : 0 <= nm < 2 ^ 64).
{ destruct (al_blocks _ _ LAWS ly4 S4 W4 mem4 md4 nm Nn (proj1 HJ4) Hinn) as (_ & Hd0 & Hdc & _).
  pose proof (req_size_pos Nn HNn) as Hq. clear - Hd0 Hdc Hq C1. lia. }
destruct LIVE4 as (L4_16 & L4_64 & L4_152 & L4_184 & L4_fl & L4_ra & L4_s0 & L4_24 & L4_32 &
L4_40 & L4_48 & L4_56 & L4_64b & L4_72 & L4_80 & L4_88 & L4_96 & L4_104).
assert (HS3 : st_ok_pi SEGS VAL E3' l_ss3
  (restrict (w_H W4) (mkst regs4 (Z_to_bv 64 (BASE + 0x1bfc)) mem4 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold l_ss3. apply pa_entry_st_ok_full.
  - rewrite HE3. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor]. unfold l_r3mf, region_ok.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    rewrite U3_9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi C1; lia|].
    split; [intros o Ho; lia|]. constructor; [|constructor].
    apply (chunk_ok_val SEGS E3' _ mf 152 8 (SOff 32 0) nm);
    [ cbn [sv_denot]; rewrite E3_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
    | clear - Hnm64; cbn; lia | cbn; lia | exact L4_152 ].
  - cbn [pairwise_disjoint all_disjoint].
    repeat match goal with |- _ /\ _ => split end; exact I.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_shc RUNP RUNC HS3 HJ4.
{ intros a (r & Hr & Ha). unfold l_ss3 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | []]. unfold l_r3mf in Ha.
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha. lia. }
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 ->
  aview SEGS (w_H W4) (ms_mem ms1) a = aview SEGS (w_H W4) mem4 a).
{ intros a Ha. apply (kept_of_frame E3' _ (w_H W4) mem4 (ms_mem ms1) (fun _ => False) HFr);
  [| exact Ha | intros []].
  intros bb wlo whi aa Hin Hr. unfold l_ss3, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | []]. injection Eq as <- <- <-. cbn [base_val] in Hr. lia. }
clear HF HFr HG.
prreg HS3 (10%bv : bv 5) R3_10. prreg HS3 (1%bv : bv 5) R3_1. prreg HS3 (2%bv : bv 5) R3_2.
prreg HS3 (3%bv : bv 5) R3_3. prreg HS3 (4%bv : bv 5) R3_4. prreg HS3 (8%bv : bv 5) R3_8.
prreg HS3 (9%bv : bv 5) R3_9. prreg HS3 (23%bv : bv 5) R3_23.
rewrite E3_32 in R3_10.
rewrite (EE3 2%nat 2%bv eq_refl), (R3p 2%bv ltac:(l_cs)), R2_2 in R3_2.
rewrite (EE3 3%nat 3%bv eq_refl), (R3p 3%bv ltac:(l_cs)), R2_3 in R3_3.
rewrite (EE3 4%nat 4%bv eq_refl), (R3p 4%bv ltac:(l_cs)), R2_4 in R3_4.
rewrite (EE3 8%nat 8%bv eq_refl), (R3p 8%bv ltac:(l_cs)), R2_8 in R3_8.
rewrite (EE3 9%nat 9%bv eq_refl), (R3p 9%bv ltac:(l_cs)), R2_9 in R3_9.
rewrite (EE3 23%nat 23%bv eq_refl), (R3p 23%bv ltac:(l_cs)), R2_23 in R3_23.
assert (LIVE3' : l_live g pos mf nm dp W4 (ms_mem ms1))
by (eapply l_live_keep; [exact Hmfb | intros a Ha; apply KEEP3; clear - Ha HSF0 HSF1 C1; lia
   | intros a Ha; apply KEEP3; clear - Ha Hmf0 Hmfb H47 Hshi C1; lia
   | unfold l_live; repeat split; assumption]).
destruct LIVE3' as (L5_16 & L5_64 & L5_152 & L5_184 & L5_fl & L5_ra & L5_s0 & L5_24 & L5_32 &
L5_40 & L5_48 & L5_56 & L5_64b & L5_72 & L5_80 & L5_88 & L5_96 & L5_104).
assert (HnotEn : ~ In (nm, Nn) (ablocks B (e_ly g) (e_S g))).
{ intros Hx. apply (l_fresh ly4 S4 W4 _ _ nm Nn _ (proj1 HJ4) Hperm4 HNn). exact Hx. }
assert (MOK3 : mo_ok MT S4 (mo_free MT)).
{ apply (mok_station MT S2 S4 _ (mo_free MT + mo_free MT) (mo_free MT) MTL MOK
    (mle_station MT S2 S3 S4 _ _ MTL MLE3 MLE4) HF0).
  clear - HT3 HF0. lia. }
pmkst HS3. rewrite (pal_free B TL).
eapply SRr_bind.
{ eapply (l_free_one g pos mf ly4 S4 W4 (ms_regs ms1) (ms_mem ms1) _
    (4 * Z.of_nat nrec + 7 + 1 + 1) 0x1c04 nm Nn HPRE HJ4 Hfrs4' Hmfb Hmf32);
  [ exact R3_2 | exact R3_8 | exact R3_3 | exact R3_4 | exact R3_1
  | right; right; left; reflexivity | exact R3_10 | exact Hinn | exact HnotEn | exact HNn
  | exact L5_ra | exact L5_s0 | clear - Hk; unfold EV_LLVMF in *; lia | exact MOK3 ]. }
cbv beta. intros W5 c5 Hwle5 (ly5 & S5 & regs5 & mem5 & md5 & -> & HJ5 & HP5 &
(nl1 & nl2 & Enb & Enb5) & Hfrs5 & MLE5 & KF5 & KS5).
assert (Hfrs5' : frames S5 = [(4, pos)]) by (rewrite Hfrs5; exact Hfrs4').
assert (LIVE5 : l_live g pos mf nm dp W5 mem5)
by (eapply l_live_keep; [exact Hmfb | exact KF5 | exact KS5
   | unfold l_live; repeat split; assumption]).
assert (Hperm5 : Permutation (ablocks B ly5 S5) (ablocks B (e_ly g) (e_S g))).
{ rewrite Enb5. rewrite Enb in Hperm4.
  apply (Permutation_cons_inv (a := (nm, Nn))).
  eapply Permutation_trans; [apply Permutation_middle | exact Hperm4]. }
assert (R4p : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs5 r = getr (ms_regs ms1) r)
by (intros r Hr; exact (l_pres r _ _ HP5 Hr)).
destruct LIVE5 as (L6_16 & L6_64 & L6_152 & L6_184 & L6_fl & L6_ra & L6_s0 & L6_24 & L6_32 &
L6_40 & L6_48 & L6_56 & L6_64b & L6_72 & L6_80 & L6_88 & L6_96 & L6_104).
(* ================ run 4: +0x1c04 .. the shadow fill call at +0x1c74 ================ *)
remember (Eimg (Ereg regs5 [Z_to_bv 64 (SFa g pos)])) as E4' eqn:HE4.
assert (HEI4 : img_env VAL A_LIM E4') by (rewrite HE4; apply Eimg_env).
assert (EE4 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E4' n = getr regs5 r)
by (intros n r Hn; rewrite HE4; apply ew_Eimg_Ereg_nat; exact Hn).
assert (E4_32 : ew E4' 32 = Z_to_bv 64 (SFa g pos))
by (rewrite HE4, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs5 _ 0)).
assert (U4_9 : bv_unsigned (ew E4' 9) = mf).
{ rewrite (EE4 9%nat 9%bv eq_refl), (R4p 9%bv ltac:(l_cs)), R3_9. unfold w64.
  apply unsigned_lit_small. clear - Hmf0 H47 Hmfb Hshi C1. lia. }
assert (U4_23 : bv_unsigned (ew E4' 23) = shadow_addr (SFa g pos)).
{ rewrite (EE4 23%nat 23%bv eq_refl), (R4p 23%bv ltac:(l_cs)), R3_23. unfold w64.
  apply unsigned_lit_small. clear - Hshlo Hshhi C1. lia. }
assert (U4_32 : bv_unsigned (ew E4' 32) = SFa g pos)
by (rewrite E4_32; apply unsigned_lit_small; clear - HSF0 HSF1 C1; lia).
destruct (proj1 (proj2 HJ5)) as (_ & _ & _ & _ & _ & EF5 & _).
assert (EFa5 : frame_addr ly5 4 pos = SFa g pos)
by (unfold SFa, frame_addr; rewrite EF5; reflexivity).
destruct (al_frames _ _ LAWS ly5 S5 W5 mem5 md5 4 pos (proj1 HJ5)
  ltac:(rewrite Hfrs5'; left; reflexivity)) as (_ & _ & HFpres5 & HFSpres5).
rewrite EFa5, HFB in HFpres5. rewrite EFa5 in HFSpres5.
change (fs_frame_bytes 4 / 8) with 128 in HFSpres5.
assert (HS4 : st_ok_pi SEGS VAL E4' l_ss4
  (restrict (w_H W5) (mkst regs5 (Z_to_bv 64 (BASE + 0x1c04)) mem5 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold l_ss4. apply pa_entry_st_ok_full.
  - rewrite HE4. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold l_r4mf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U4_9. split; [clear - Hmf0 C1; lia|]. split; [clear - Hmf0 H47 Hmfb Hshi C1; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor; [|constructor]].
      * apply (chunk_ok_val SEGS E4' _ mf 16 8 (SOff 32 0) (SFa g pos));
        [ cbn [sv_denot]; rewrite E4_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | clear - HSF0 HSF1 C1; cbn; lia | cbn; lia | exact L6_16 ].
      * apply (chunk_ok_val SEGS E4' _ mf 64 8 (SOff 32 0) (SFa g pos));
        [ cbn [sv_denot]; rewrite E4_32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
        | clear - HSF0 HSF1 C1; cbn; lia | cbn; lia | exact L6_64 ].
    + unfold l_r4sf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U4_32. split; [clear - HSF0; lia|]. split; [clear - HSF1 C1; lia|].
      split; [|constructor]. intros o Ho. apply (apresent_writable SEGS).
      exact (proj1 (HFpres5 (SFa g pos + o) ltac:(clear - Ho; lia))).
    + unfold l_r4sh, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U4_23. split; [clear - Hshlo; lia|]. split; [clear - Hshhi C1; lia|].
      split; [|constructor]. intros o Ho. apply (apresent_writable SEGS).
      exact (proj1 (HFSpres5 o ltac:(clear - Ho; lia))).
  - cbn [pairwise_disjoint all_disjoint]. unfold l_r4mf, l_r4sf, l_r4sh, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U4_9, U4_23, U4_32.
    repeat match goal with |- _ /\ _ => split end; try exact I.
    + right. clear - HSF1 Hmf0 C1. lia.
    + right. clear - Hshhi Hmf0 C1. lia.
    + clear - HSFsh. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    unfold afact_ok, HPTR. cbn [af_lo af_hi af_al2].
    rewrite U4_32, Z.pow_0_r, Z.mod_1_r.
    repeat match goal with |- _ /\ _ => split end;
    first [ exact I | reflexivity | clear - HSF0 HSF1 C1; lia ]. }
paj_run_shc RUNP RUNC HS4 HJ5.
{ intros a (r & Hr & Ha). unfold l_ss4 in Hr. cbn [ss_mem In] in Hr.
  destruct Hr as [<- | [<- | [<- | []]]];
  unfold l_r4mf, l_r4sf, l_r4sh in Ha;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha.
  - lia.
  - rewrite U4_32 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
    left. unfold in_zr. cbn [fst snd]. rewrite EFa5, HFB. clear - Ha. lia.
  - rewrite U4_23 in Ha. right; right; right. exists 4, pos. split; [left; reflexivity|].
    right. unfold in_zr. cbn [fst snd]. rewrite EFa5.
    change (fs_frame_bytes 4 / 8) with 128. clear - Ha. lia. }
assert (KEEP4 : forall a, 0 <= a < 2 ^ 64 ->
  ~ (SFa g pos <= a < SFa g pos + 8) ->
  ~ (shadow_addr (SFa g pos) + 44 <= a < shadow_addr (SFa g pos) + 82) ->
  aview SEGS (w_H W5) (ms_mem ms2) a = aview SEGS (w_H W5) mem5 a).
{ intros a Ha Hw1 Hw2.
  apply (kept_of_frame E4' _ (w_H W5) mem5 (ms_mem ms2)
    (fun x => (SFa g pos <= x < SFa g pos + 8) \/
              (shadow_addr (SFa g pos) + 44 <= x < shadow_addr (SFa g pos) + 82)) HFr);
  [| exact Ha | intros [Hx | Hx]; [exact (Hw1 Hx) | exact (Hw2 Hx)]].
  intros bb wlo whi aa Hin Hr. unfold l_ss4, windows in Hin. cbn in Hin.
  destruct Hin as [Eq | [Eq | [Eq | []]]]; injection Eq as <- <- <-;
  cbn [base_val] in Hr; rewrite ?U4_9, ?U4_23, ?U4_32 in Hr.
  - lia.
  - left. clear - Hr. lia.
  - right. clear - Hr. lia. }
clear HF HFr HG.
prreg HS4 (10%bv : bv 5) R4_10. prreg HS4 (11%bv : bv 5) R4_11. prreg HS4 (1%bv : bv 5) R4_1.
prreg HS4 (2%bv : bv 5) R4_2. prreg HS4 (3%bv : bv 5) R4_3. prreg HS4 (4%bv : bv 5) R4_4.
prreg HS4 (8%bv : bv 5) R4_8. prreg HS4 (20%bv : bv 5) R4_20.
rewrite (EE4 23%nat 23%bv eq_refl), (R4p 23%bv ltac:(l_cs)), R3_23 in R4_10.
rewrite E4_32 in R4_20.
rewrite (EE4 2%nat 2%bv eq_refl), (R4p 2%bv ltac:(l_cs)), R3_2 in R4_2.
rewrite (EE4 3%nat 3%bv eq_refl), (R4p 3%bv ltac:(l_cs)), R3_3 in R4_3.
rewrite (EE4 4%nat 4%bv eq_refl), (R4p 4%bv ltac:(l_cs)), R3_4 in R4_4.
rewrite (EE4 8%nat 8%bv eq_refl), (R4p 8%bv ltac:(l_cs)), R3_8 in R4_8.
assert (KEEPF : forall a, SFa g pos + 8 <= a < SFa g pos + 1024 ->
  aview SEGS (w_H W5) (ms_mem ms2) a = aview SEGS (w_H W5) mem5 a).
{ intros a Ha. apply KEEP4; [clear - Ha HSF0 HSF1 C1; lia | clear - Ha; lia
  | clear - Ha HSFsh; lia]. }
assert (KEEPS : forall a, mf <= a < e_sp0 g ->
  aview SEGS (w_H W5) (ms_mem ms2) a = aview SEGS (w_H W5) mem5 a).
{ intros a Ha. apply KEEP4;
  [ clear - Ha Hmf0 Hmfb H47 Hshi C1; lia | clear - Ha Hmf0 HSF1 C1; lia
  | clear - Ha Hmf0 Hshhi C1; lia ]. }
assert (LIVE6 : l_live g pos mf nm dp W5 (ms_mem ms2))
by (eapply l_live_keep; [exact Hmfb | exact KEEPF | exact KEEPS
   | unfold l_live; repeat split; assumption]).
destruct LIVE6 as (L7_16 & L7_64 & L7_152 & L7_184 & L7_fl & L7_ra & L7_s0 & L7_24 & L7_32 &
L7_40 & L7_48 & L7_56 & L7_64b & L7_72 & L7_80 & L7_88 & L7_96 & L7_104).
assert (Ura5 : raZ (ms_regs ms2) = BASE + 0x1c78)
by (unfold raZ; rewrite R4_1; apply unsigned_lit_small; clear - HBASE; lia).
pmkst HS4.
(* ================ the shadow fill ================ *)
eapply SRr_bind.
{ eapply (l_shadow g pos mf ly5 S5 W5 (ms_regs ms2) (ms_mem ms2) _ _ HPRE HJ5 Hfrs5' Hmfb Hmf32
    R4_2 R4_3 R4_4);
  [ rewrite R4_1; apply ret_ok_codeptr_v; [clear - HBASE; lia | reflexivity]
  | exact R4_10 | exact R4_11 ]. }
cbv beta. intros W6 c6 Hwle6 (-> & regs6 & mem6 & md6 & -> & HJ6 & HP6 & KEEP6).
rewrite Ura5.
assert (R6p : forall (r : bv 5), acallee_saved (bv_unsigned r) -> getr regs6 r = getr (ms_regs ms2) r)
by (intros r Hr; exact (l_pres r _ _ HP6 Hr)).
assert (LIVE7 : l_live g pos mf nm dp W5 mem6).
{ eapply (l_live_keep g pos mf nm dp W5 W5 (ms_mem ms2) mem6);
  [ exact Hmfb
  | intros a Ha; apply KEEP6; [clear - Ha HSF0 HSF1 C1; lia | clear - Ha HSFsh; lia]
  | intros a Ha; apply KEEP6;
    [clear - Ha Hmf0 Hmfb H47 Hshi C1; lia | clear - Ha Hmf0 Hshhi C1; lia]
  | unfold l_live; repeat split; assumption ]. }
destruct LIVE7 as (L8_16 & L8_64 & L8_152 & L8_184 & L8_fl & L8_ra & L8_s0 & L8_24 & L8_32 &
L8_40 & L8_48 & L8_56 & L8_64b & L8_72 & L8_80 & L8_88 & L8_96 & L8_104).
(* ================ run 5: +0x1c78, the release and the epilogue ================ *)
destruct (al_flag _ _ LAWS ly5 S5 W5 mem6 md6 4 pos (proj1 HJ6)
  ltac:(rewrite Hfrs5'; left; reflexivity)) as (HFLpres & HFLown & HFLapp & HFLceil).
destruct (al_frames _ _ LAWS ly5 S5 W5 mem6 md6 4 pos (proj1 HJ6)
  ltac:(rewrite Hfrs5'; left; reflexivity)) as (_ & _ & HFpres6 & _).
rewrite EFa5, HFB in HFpres6.
assert (EFL5 : flag_addr ly5 4 pos = flag_addr (e_ly g) 4 pos)
by (unfold flag_addr; rewrite EF5; reflexivity).
rewrite EFL5 in HFLpres, HFLown, HFLapp, HFLceil.
assert (HFLF : ~ (SFa g pos <= flag_addr (e_ly g) 4 pos < SFa g pos + 1024))
by (intros Hx; exact (proj2 (HFpres6 (flag_addr (e_ly g) 4 pos) Hx) HFLown)).
assert (HFL64 : 0 <= flag_addr (e_ly g) 4 pos < 2 ^ 64)
by (unfold app_addr, in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in HFLapp; clear - HFLapp C1; lia).
remember (Eimg (Ereg regs6 [Z_to_bv 64 (flag_addr (e_ly g) 4 pos); getr (e_regs g) 1;
getr (e_regs g) 8; getr (e_regs g) 9; getr (e_regs g) 18; getr (e_regs g) 19; getr (e_regs g) 20;
getr (e_regs g) 21; getr (e_regs g) 22; getr (e_regs g) 23; getr (e_regs g) 24; getr (e_regs g) 25;
getr (e_regs g) 26; getr (e_regs g) 27])) as E5' eqn:HE5.
assert (HEI5 : img_env VAL A_LIM E5') by (rewrite HE5; apply Eimg_env).
assert (EE5 : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E5' n = getr regs6 r)
by (intros n r Hn; rewrite HE5; apply ew_Eimg_Ereg_nat; exact Hn).
assert (X32 : ew E5' 32 = Z_to_bv 64 (flag_addr (e_ly g) 4 pos))
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 0)).
assert (X33 : ew E5' 33 = getr (e_regs g) 1)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 1)).
assert (X34 : ew E5' 34 = getr (e_regs g) 8)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 2)).
assert (X35 : ew E5' 35 = getr (e_regs g) 9)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 3)).
assert (X36 : ew E5' 36 = getr (e_regs g) 18)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 4)).
assert (X37 : ew E5' 37 = getr (e_regs g) 19)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 5)).
assert (X38 : ew E5' 38 = getr (e_regs g) 20)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 6)).
assert (X39 : ew E5' 39 = getr (e_regs g) 21)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 7)).
assert (X40 : ew E5' 40 = getr (e_regs g) 22)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 8)).
assert (X41 : ew E5' 41 = getr (e_regs g) 23)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 9)).
assert (X42 : ew E5' 42 = getr (e_regs g) 24)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 10)).
assert (X43 : ew E5' 43 = getr (e_regs g) 25)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 11)).
assert (X44 : ew E5' 44 = getr (e_regs g) 26)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 12)).
assert (X45 : ew E5' 45 = getr (e_regs g) 27)
by (rewrite HE5, Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs6 _ 13)).
assert (RG : forall r : bv 5, 0 <= bv_unsigned (getr (e_regs g) r) < 2 ^ (8 * Z.of_N 8)).
{ intros r. pose proof (bv_unsigned_in_range 64 (getr (e_regs g) r)) as Hr.
  change (bv_modulus 64) with (2 ^ (8 * Z.of_N 8)) in Hr. exact Hr. }
assert (U5_32 : bv_unsigned (ew E5' 32) = flag_addr (e_ly g) 4 pos)
by (rewrite X32; apply unsigned_lit_small; clear - HFL64; lia).
assert (U5_20 : bv_unsigned (ew E5' 20) = SFa g pos).
{ rewrite (EE5 20%nat 20%bv eq_refl), (R6p 20%bv ltac:(l_cs)), R4_20.
  apply unsigned_lit_small. clear - HSF0 HSF1 C1. lia. }
assert (U5_8 : bv_unsigned (ew E5' 8) = e_sp0 g).
{ rewrite (EE5 8%nat 8%bv eq_refl), (R6p 8%bv ltac:(l_cs)), R4_8. unfold w64.
  apply unsigned_lit_small. clear - Hmf0 Hmfb H47 Hshi C1. lia. }
assert (HS5 : st_ok_pi SEGS VAL E5' l_ss5
  (restrict (w_H W5) (mkst regs6 (Z_to_bv 64 (BASE + 0x1c78)) mem6 (seg_rom SEGS)))).
{ rewrite restrict_mkst_fx. unfold l_ss5. apply pa_entry_st_ok_full.
  - rewrite HE5. apply regs_ok_Eimg_Ereg.
  - vm_compute. reflexivity.
  - constructor; [|constructor; [|constructor; [|constructor]]].
    + unfold l_r5fl, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U5_32. split; [clear - HFL64; lia|]. split; [clear - HFL64; lia|].
      split; [|constructor]. intros o Ho. apply (apresent_writable SEGS).
      replace (flag_addr (e_ly g) 4 pos + o) with (flag_addr (e_ly g) 4 pos)
        by (clear - Ho; lia).
      exact HFLpres.
    + unfold l_r5sf, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U5_20. split; [clear - HSF0; lia|]. split; [clear - HSF1 C1; lia|].
      split; [intros o Ho; lia|]. constructor; [|constructor].
      apply (chunk_ok_val SEGS E5' _ (SFa g pos) 1016 8 (SOff 32 0) (flag_addr (e_ly g) 4 pos));
      [ cbn [sv_denot]; rewrite X32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity
      | clear - HFL64; cbn; lia | cbn; lia | exact L8_fl ].
    + unfold l_r5sv, region_ok.
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
      rewrite U5_8. split; [clear - Hmf0 Hmfb C1; lia|].
      split; [clear - Hmf0 Hmfb H47 Hshi C1; lia|].
      split; [intros o Ho; lia|].
      repeat apply Forall_cons; try apply Forall_nil.
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-8) 8 (SOff 33 0) RA_LLVMF);
        [ cbn [sv_denot]; rewrite X33, Z.add_0_r, Hraz; reflexivity
        | rewrite <- Hraz; apply RG | cbn; lia
        | replace (e_sp0 g + -8) with (e_sp0 g - 8) by (clear; lia); exact L8_ra ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-16) 8 (SOff 34 0) (s0Z (e_regs g)));
        [ cbn [sv_denot]; rewrite X34, Z.add_0_r; reflexivity
        | unfold s0Z; apply RG | cbn; lia
        | replace (e_sp0 g + -16) with (e_sp0 g - 16) by (clear; lia); exact L8_s0 ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-24) 8 (SOff 35 0)
          (bv_unsigned (getr (e_regs g) 9)));
        [ cbn [sv_denot]; rewrite X35, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -24) with (e_sp0 g - 24) by (clear; lia); exact L8_24 ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-32) 8 (SOff 36 0)
          (bv_unsigned (getr (e_regs g) 18)));
        [ cbn [sv_denot]; rewrite X36, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -32) with (e_sp0 g - 32) by (clear; lia); exact L8_32 ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-40) 8 (SOff 37 0)
          (bv_unsigned (getr (e_regs g) 19)));
        [ cbn [sv_denot]; rewrite X37, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -40) with (e_sp0 g - 40) by (clear; lia); exact L8_40 ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-48) 8 (SOff 38 0)
          (bv_unsigned (getr (e_regs g) 20)));
        [ cbn [sv_denot]; rewrite X38, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -48) with (e_sp0 g - 48) by (clear; lia); exact L8_48 ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-56) 8 (SOff 39 0)
          (bv_unsigned (getr (e_regs g) 21)));
        [ cbn [sv_denot]; rewrite X39, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -56) with (e_sp0 g - 56) by (clear; lia); exact L8_56 ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-64) 8 (SOff 40 0)
          (bv_unsigned (getr (e_regs g) 22)));
        [ cbn [sv_denot]; rewrite X40, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -64) with (e_sp0 g - 64) by (clear; lia); exact L8_64b ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-72) 8 (SOff 41 0)
          (bv_unsigned (getr (e_regs g) 23)));
        [ cbn [sv_denot]; rewrite X41, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -72) with (e_sp0 g - 72) by (clear; lia); exact L8_72 ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-80) 8 (SOff 42 0)
          (bv_unsigned (getr (e_regs g) 24)));
        [ cbn [sv_denot]; rewrite X42, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -80) with (e_sp0 g - 80) by (clear; lia); exact L8_80 ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-88) 8 (SOff 43 0)
          (bv_unsigned (getr (e_regs g) 25)));
        [ cbn [sv_denot]; rewrite X43, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -88) with (e_sp0 g - 88) by (clear; lia); exact L8_88 ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-96) 8 (SOff 44 0)
          (bv_unsigned (getr (e_regs g) 26)));
        [ cbn [sv_denot]; rewrite X44, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -96) with (e_sp0 g - 96) by (clear; lia); exact L8_96 ].
      * apply (chunk_ok_val SEGS E5' _ (e_sp0 g) (-104) 8 (SOff 45 0)
          (bv_unsigned (getr (e_regs g) 27)));
        [ cbn [sv_denot]; rewrite X45, Z.add_0_r; reflexivity
        | apply RG | cbn; lia
        | replace (e_sp0 g + -104) with (e_sp0 g - 104) by (clear; lia); exact L8_104 ].
  - cbn [pairwise_disjoint all_disjoint]. unfold l_r5fl, l_r5sf, l_r5sv, extent_disjoint.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]. rewrite U5_32, U5_20, U5_8.
    repeat match goal with |- _ /\ _ => split end; try exact I.
    + clear - HFLF HSF0 HSF1 C1. lia.
    + left. clear - HFLapp HFLceil Hmf0 Hmfb C1.
      unfold app_addr, in_app, ASAN_CEIL, kLowShadowBeg, kHighMemBeg in *. lia.
    + left. clear - HSF1 Hmf0 Hmfb C1. lia.
  - unfold facts_ok. cbn [f_atoms f_conds f_alias atoms_ok conds_ok alias_ok].
    split; [exact I | split; exact I]. }
paj_run_flag_sh RUNF HS5 HJ6.
- lia.
- intros a (r & Hr0 & Hr).
  lazymatch type of Hr0 with
  | In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hr0
  end.
  destruct Hr0 as [<- | [<- | [<- | []]]];
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U5_32, ?U5_20, ?U5_8 in Hr.
  + right. rewrite EFL5. clear - Hr. lia.
  + exfalso. clear - Hr. lia.
  + exfalso. clear - Hr. lia.
- intros msr HSr.
  pose proof (st_ok_pi_region_nth E5' _ msr 0%nat _ HSr eq_refl) as HR.
  pose proof (field_of_region E5' (ms_mem msr) 32 (flag_addr (e_ly g) 4 pos) _ 0 1 0 1 0 1%N
    (SLit 0) 0 HR U5_32 ltac:(left; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)) as V.
  pose proof (V 0%nat ltac:(cbn; lia)) as V0. cbn [Z.of_nat] in V0. rewrite !Z.add_0_r in V0.
  rewrite EFL5. exact V0.
- cbn [ms_mem mkst] in HF, HFr, HG.
  prreg HS5 (1%bv : bv 5) Q1. prreg HS5 (10%bv : bv 5) Q10. prreg HS5 (2%bv : bv 5) Q2.
  prreg HS5 (3%bv : bv 5) Q3. prreg HS5 (4%bv : bv 5) Q4. prreg HS5 (8%bv : bv 5) Q8.
  prreg HS5 (9%bv : bv 5) Q9. prreg HS5 (18%bv : bv 5) Q18. prreg HS5 (19%bv : bv 5) Q19.
  prreg HS5 (20%bv : bv 5) Q20. prreg HS5 (21%bv : bv 5) Q21. prreg HS5 (22%bv : bv 5) Q22.
  prreg HS5 (23%bv : bv 5) Q23. prreg HS5 (24%bv : bv 5) Q24. prreg HS5 (25%bv : bv 5) Q25.
  prreg HS5 (26%bv : bv 5) Q26. prreg HS5 (27%bv : bv 5) Q27.
  assert (Q1' : v_jalr (getr (ms_regs ms3) 1) 0 = getr (e_regs g) 1)
  by (rewrite Q1, X33; exact Hraok0).
  eapply (RET W5 E5' _ _ _ _ HS5 eq_refl ltac:(vm_compute; reflexivity)).
  intros mat'. cbv beta. rewrite Q1'.
  unfold inv_ret, tLLVMFuzzerTestOneInput_post.
  exists ly5, (stack_free_state 4 pos S5). do 3 eexists.
  exists (4 * Z.of_nat nrec + 7 + 1 + 1 + 1).
  split.
  { unfold cfg_at, w64. rewrite <- Hraz, Z_to_bv_bv_unsigned. reflexivity. }
  pose proof (ajournal_materialize SEGS B LAWS Hsegs LLVMF_STK (e_sp0 g) []
    (e_ly g) (e_S g) (e_W g) (e_mem g) (e_md g) [] ly5 (stack_free_state 4 pos S5) W5
    (ms_mem ms3) _ _ mat' HJ6) as HJM.
  split; [cbn [ms_mem mkst];
          exact (AJ_FP_NIL _ _ [sink_token] _ _ _ _ _ _ _ _ _ _ _ _ HJM)|].
  split; [clear - Hk HEV; unfold EV_LLVMF in *; lia|].
  split.
  { apply aregs_preserved_eqs.
    - rewrite Q2. apply bv_eq. rewrite U5_8. unfold e_sp0, spZ. reflexivity.
    - rewrite Q3, (EE5 3%nat 3%bv eq_refl), (R6p 3%bv ltac:(l_cs)), R4_3. symmetry. exact Hgp0.
    - rewrite Q4, (EE5 4%nat 4%bv eq_refl), (R6p 4%bv ltac:(l_cs)), R4_4. symmetry. exact Htp0.
    - rewrite Q8, X34. reflexivity.
    - rewrite Q9, X35. reflexivity.
    - rewrite Q18, X36. reflexivity.
    - rewrite Q19, X37. reflexivity.
    - rewrite Q20, X38. reflexivity.
    - rewrite Q21, X39. reflexivity.
    - rewrite Q22, X40. reflexivity.
    - rewrite Q23, X41. reflexivity.
    - rewrite Q24, X42. reflexivity.
    - rewrite Q25, X43. reflexivity.
    - rewrite Q26, X44. reflexivity.
    - rewrite Q27, X45. reflexivity. }
  split; [rewrite Q10; reflexivity|].
  split.
  { unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly5 S5). exact Hperm5. }
  destruct (AJ_NIL_IO _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJM) as [Efds Efs].
  split; [intros fd; rewrite Efds; reflexivity|].
  split; [cbn [ll_fs]; exact Efs|].
  split; [reflexivity|]. split; [reflexivity|].
  split; [cbn [ll_fs]; exact Hsort0|].
  split.
  { eapply (ASINK_NONE_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJM sink_closed_nil). exact Hsnk0. }
  split.
  { eapply (AMETA_INV_KEPT _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJM). exact Hmeta0. }
  split.
  { unfold stack_free_state. apply (mo_le_set_fs_r MT MTF).
    eapply (mo_le_mono MT MTL).
    - exact (mle_station MT (e_S g) S2 S5 _ _ MTL MLE
        (mle_station MT S2 S4 S5 _ _ MTL (mle_station MT S2 S3 S4 _ _ MTL MLE3 MLE4) MLE5)).
    - pose proof (HXN (e_n g)) as HX. clear - HX HM0 HF0 Hnrec. unfold EV_LLVMF in *. nia. }
  intros i Hi.
  destruct Hinp as [[Hn0' _] | [[Hnl Hnh] Hine]]; [clear - Hi Hn0'; lia|].
  pose proof HJM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & FB & _).
  assert (HinF : In (e_p g, e_n g) (ablocks B ly5 (stack_free_state 4 pos S5))).
  { unfold ablocks. rewrite blocks_stack_free_state. fold (ablocks B ly5 S5).
    eapply Permutation_in; [apply Permutation_sym; exact Hperm5 | exact Hine]. }
  pose proof (req_size_pos (e_n g) ltac:(clear - Hnl; lia)) as Hq.
  exact (FB (e_p g) (e_n g) i Hine HinF ltac:(clear - Hi Hq; lia) (fun H => inFP_nil _ H)).
Qed.

Lemma seg_L : seg_L_stmt B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS.
Proof. exact seg_L_holds. Qed.

Check (seg_L : seg_L_stmt B MT XM_LIB XN_LIB RLO RHI RA_LLVMF A_EMPTY LLVMF_STK EV_LIB LIVE_LIB
asink_syms_T KS asink_none ameta_inv arodata_okS).

End c.
End b.
End a.

(* audit: the Section hypotheses are arguments of the closed lemma, not axioms *)
Print Assumptions seg_L.
