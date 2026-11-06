(* fuzz_preset, slice S5b, lane VnumE (worker a Theorem Labs lane): parse_value's NUMBER ARM in image A from the token scan's
   exit to the arm's join - listing rows 267..328 of the neutral per-function listing of the pinned rebuilt image A
   (parse_value's disassembly in the #102 pin A' image; row 1 is the entry 0x85f10).
   rule 24: no function is proved here (kind: segment lemma). The entry state is the boundary vrd_num266_a defined
   below (lane VnumD's scan concludes into it), every callee is a published text or a named Section hypothesis, and
   the conclusion is lib/A/VrdNum.v's vrd_ref_a / vrd_epi_a.

   THE BOUNDARY AT ROW 266. The scan (rows 193..208) leaves through row 208 `j` to row 266 `mv s6, a2` when it reaches
   text + len, or through rows 201 / 204 to row 267 when the byte is outside PjGrammar.numch. Both exits reach row 267
   with s6 = p' + |txt|, txt = fst (vrd_num_tok (rest_atR tb text p')) (at row 266 s6 is set to a2 = text + len =
   p' + |txt|), so the boundary has ONE pc, row 267 (VnumD's offer). The state is stated RELATIVE TO THE DISPATCH
   STATE: VrdPro.vrd_disp_body (the dispatch state without its pc equation, a working branch 5c2e03a3e34) at the
   number arm with its witnesses named, the journal at the current state with the same allocator state, the memory
   equal to the dispatch memory outside the two places rows 157..266 write (the frame's 8 shadow bytes, row 157; the
   stack slots [sp, sp + 32), row 192), the registers rows 157..266 leave alone (VrdNum.vrd_kept_regs), s5 = -1,
   s6 = p' + |txt|, and row 192's spill.

   THE GENERIC MEMORY INVARIANT (a Theorem Labs lane's 12:19Z ruling; lane A2NumP). REASON: an SRr post is opaque once Qed, so
   an end-state memory invariant must be in the segment's STATEMENT; the generic SRr_memnorm was measured NOT provable
   (a Theorem Labs lane), so it cannot be added afterwards. Every segment here has a _P twin with P : (word -> option byte) ->
   Prop and YC80x.srr_inv_laws (the runs: YC1fPx's paj_run_x_inv, YC80xf_inv's paj_run_xf_inv / paj_run_to_xf_inv),
   YSRrMemnorm.srr_inv_call (the calls: fuzz_malloc's m-form post, __asan_memcpy through YGcallMxmn.aj_intrin_at_xm,
   strtod's row) and, for the strtod row's memnorm entry premise, YSRrMemnorm.srr_inv_mn. vrd_seg_267 and vrd_seg_271
   survive BYTE-IDENTICAL as their corollaries at P := fun _ => True. vrd_seg_284 and vrd_num_tail do NOT: their
   proofs needed the Section hypothesis that claimed memnorm at every allocator state, which is unprovable and is
   deleted; at P := fun _ => True, srr_inv_mn would be that same claim. Nothing outside this file cited either. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YP0m YP0e YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YGcfNames YCbqG YP0b YPsym YC4aP YGcfRoomPre YGcfRoomKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK0h YK0i YK14 YK1b YK1a YK0j YN3v YG0s YP07 YP0a YG0p YP0d YP0c YC80 YImgTop YC1fP YC80x YC1fPx YC80xf
YGcallx YCbqGcall YGcallSx YGcallMx FCiface YStrtodRowX YFclsStep YSRrMemnorm YC80xf_inv YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import
PRH_Base PRH_Reader PRH_FnReader PRH_Charge PRH_FnParse PRH_FnAlloc.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import Img0 Listing_prog PAImg_prog VrdPro VrdNum.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import strtod_c strtod_row S1Ledger.
Import ListNotations.
Local Open Scope Z_scope.

Section t. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}
  {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B prh_pst ARx).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).

(* ---- THE BOUNDARY AT ROW 266 / 267 (A 0x86330 / 0x86334) ----
   pc = row 267 (`sub a0, s6, a0`). The witnesses: pos p' k1 ly S Hp regs1 mem1 md1 are the dispatch state's
   (vrd_disp_body), regs mem md k the current state's, txt r the token and the rest after it. Besides the dispatch body
   it carries the call's own premises at parse_value's entry (vrd_num_a_stmt's fpre / argument registers / rd_pre),
   the token as vrd_num_tok measures it, the journal at the current state (rows 157..266 allocate nothing, so ly S Hp
   are the dispatch's), the memory against the dispatch's outside the frame's 8 shadow bytes and the stack slots
   [sp, sp + 32), presence growing, the fourteen registers rows 157..266 leave alone, s5 = -1, s6 = p' + |txt|, and
   the endptr cell's address fr + 32 that row 192 spilled at sp + 16. *)
Definition vrd_num266_a
  (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)) (CTX0 : list (list Z)) (CW : list (list Z))
  (e q v text len p : Z) (d : nat) (tb : list Z)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : world segs -> config -> Prop :=
  fun W c =>
  exists (pos p' k1 k : Z) (ly : alayout) (S : astate) (Hp : list Z)
         (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model) (txt r : list Z),
  c = cfg_at segs (BASE + vrd_row 267) regs mem md /\
  (* the call's own premises, at parse_value's entry *)
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch /\
  getr regs0 10 = w64 q /\ getr regs0 11 = w64 v /\
  rd_pre B (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 Lam peak cnt fail ran most own e q text len p d tb v /\
  (* the dispatch state *)
  vrd_disp_body B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    VA_num pos p' k1 ly S Hp W regs1 mem1 md1 /\
  (* the token rows 163..208 accepted, and the rest after it *)
  vrd_num_tok (rest_atR tb text p') = Some (txt, r) /\
  rest_atR tb text (p' + Z.of_nat (length txt)) = r /\
  (* rows 157..266, from the dispatch state *)
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k /\
  (forall a, 0 <= a < 2 ^ 64 ->
     ~ (SHADOW_OFF + frame_addr ly 0 pos / 8 <= a < SHADOW_OFF + frame_addr ly 0 pos / 8 + 8) ->
     ~ (spZ regs1 <= a < spZ regs1 + 32) ->
     aview segs (w_H W) mem a = aview segs (w_H W) mem1 a) /\
  (forall a, apresent (w_H W) mem1 a -> apresent (w_H W) mem a) /\
  vrd_kept_regs regs regs1 /\
  getr regs 21 = w64 (-1) /\ getr regs 22 = w64 (p' + Z.of_nat (length txt)) /\
  val_mem segs (rdW W mem) (spZ regs1 + 16) 8 (frame_addr ly 0 pos + 32).

(* ======================================================================================================== *)
(* THE WALK, rows 267..328                                                                                  *)
(* ======================================================================================================== *)
Context {HL : Z}.
Hypothesis LAWS : AR_laws_x segs B ARx HL.
#[local] Notation VAL := (@pa_val _ A_prog_listing PI_prog_A).

(* ---- rows 267..270: a0 = s6 - a0 = |txt| (n), spilled at sp + 24, a0 = n + 1, `jal fuzz_malloc` ----
   The state: the stack slots [sp, sp + 32) of the 32-aligned frame base (s1 = sp), writable from sp + 8, the
   endptr cell's address fr + 32 at sp + 16 (row 192's spill). No instrumented access. *)
Definition vrd_267_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 0 32 24 32 [YP09.mkChunk 16 (CVal 8 (SOff 26 32))] ].
Definition vrd_267_facts : facts := mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 5) ] [] [].
Definition ss_vrd_267 : sstate := mkSS (vrd_row 267) sr_atoms vrd_267_regions None vrd_267_facts.

Lemma vrd_st_267 : forall (W : world segs) regs mem (sp fr : Z),
  getr regs 9 = w64 sp -> getr regs 26 = w64 fr -> 2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 ->
  0 <= fr -> fr + 32 < 2 ^ 64 ->
  val_mem segs (rdW W mem) (sp + 16) 8 (fr + 32) ->
  (forall o, 24 <= o < 32 -> writable_at segs (rdW W mem) (sp + o)) ->
  st_ok_pi segs VAL (vrd_E regs) ss_vrd_267
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row 267)) mem (seg_rom segs))).
Proof.
intros W regs mem sp fr R9 R26 Hsp Hal Hfr0 Hfr V16 Wst. rewrite restrict_mkst_fx.
assert (E9 : ew (vrd_E regs) 9 = getr regs 9)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E26 : ew (vrd_E regs) 26 = getr regs 26)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 26 26%bv eq_refl)).
apply pa_entry_st_ok_full.
- apply regs_ok_Eimg_Ereg.
- vm_compute. reflexivity.
- unfold vrd_267_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite E9, R9. unfold w64. rewrite unsigned_lit_small by lia.
  split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Wst o Ho)|].
  repeat constructor.
  apply (chunk_ok_val segs _ _ sp 16 8 (SOff 26 32) (fr + 32));
    [cbn [sv_denot]; rewrite E26, R26; unfold w64; rewrite unsigned_lit_small by lia; reflexivity
    | cbn; lia | lia | exact V16].
- apply pairwise_disjoint_of_extents. unfold vrd_267_regions, extent_of_region.
  cbn [map YP09.r_base YP09.r_lo YP09.r_hi zpairwise_disjoint zall_disjoint]. tauto.
- split; [|split; [exact I | exact I]].
  cbn [vrd_267_facts f_atoms atoms_ok]. split; [|exact I].
  unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite E9, R9. unfold w64. rewrite unsigned_lit_small by lia.
  change (2 ^ 5) with 32. split; [lia|]. split; [exact Hal | lia].
Qed.

(* IMAGE FACT (an instance proves it of its own PrhImg: prh_pst's cells (alloc.c's six statics and fuzz_preset.c's g_own_ran_out) are image bytes, S1ImgA.v
   pst_in_img_A at prh_img_A): the statics the journal exempts are image bytes *)
Hypothesis PST_IMG : forall a, Exists (in_zr a) prh_pst -> in_img segs a.

(* the ledger survives any change at or above a bound that clears the allocator's blocks by a word: its statics are
   image bytes and its heads are the 8 bytes at the base of an allocator block, both below *)
Lemma vrd_ledger_hi : forall lo ly S Hp W mem mem' memX mdX Lam peak cnt fail ran most own,
  alloc_ceiling + 8 <= lo ->
  ARx ly S Hp W memX mdX -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < lo -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros lo ly S Hp W mem mem' memX mdX Lam peak cnt fail ran most own Hlo HAR HLd HK.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran most own HLd).
- intros a Ha. pose proof (@pa_segs_low _ _ PI_prog_A a (PST_IMG a Ha)). apply HK. lia.
- intros a k i Hin Hi.
  destruct (prh_ledger_hblock B ly S Hp W mem Lam peak cnt fail ran a k most own HLd Hin) as (Hk0 & Hab & _).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W memX mdX (a - cf_head) (k + cf_head) HAR Hab) as (Hal & H4096 & Hc & _).
  pose proof cf_head_nonneg as Hh.
  assert (Hr1 : 1 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  apply HK. lia.
- intros a k _ H. exact H.
- apply Permutation_refl.
Qed.

(* the read-only view survives any change at or above alloc_ceiling *)
Lemma vrd_rod_hi : forall (W W' : world segs) m m',
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) m) ->
  (forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W') m' a = aview segs (w_H W) m a) ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W') m').
Proof.
intros W W' m m' H HA a Hro Hn He.
assert (Hi : in_img segs a).
{ destruct Hro as [(sg & Hin & _ & Hr) | Hr]; [exists sg; split; [exact Hin | exact Hr] | exact (@pa_relro_img _ _ PI_prog_A a Hr)]. }
pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hl.
pose proof asan_consts as (C1 & _ & _ & _ & C5). rewrite HA by lia. exact (H a Hro Hn He).
Qed.

(* a frame-pointer chain read from v survives a change of the bytes below v - 16: the chain reads only
   [v - 16, ly_top ly) *)
Lemma vrd_achain_hi : forall ly (rd rd' : reader) sp v ch,
  achain ly rd sp v ch -> (forall a, v - 16 <= a -> a < ly_top ly -> rd' a = rd a) ->
  achain ly rd' sp v ch.
Proof.
intros ly rd rd' sp v ch [H | (H1 & H2 & H3 & H4 & H5)] HK; [left; exact H|].
right. split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [|exact H5].
eapply (fpchain_ext (rdword rd) (rdword rd') v (ly_top ly) ch); [| lia | exact H4].
intros a Ha Ha2. unfold rdword. rewrite !HK by lia. reflexivity.
Qed.

(* zcanon absorbs a zcanon in either argument of a sum and in the right argument of a product *)
Lemma vrd_can_add_l : forall x y, zcanon (zcanon x + y) = zcanon (x + y).
Proof. intros x y. unfold zcanon, M64. apply Zplus_mod_idemp_l. Qed.
Lemma vrd_can_add_r : forall x y, zcanon (x + zcanon y) = zcanon (x + y).
Proof. intros x y. unfold zcanon, M64. apply Zplus_mod_idemp_r. Qed.
Lemma vrd_can_mul_r : forall x y, zcanon (x * zcanon y) = zcanon (x * y).
Proof. intros x y. unfold zcanon, M64. apply Zmult_mod_idemp_r. Qed.
Lemma vrd_can_add_mod : forall x y, zcanon (x + y * 2 ^ 64) = zcanon x.
Proof. intros x y. unfold zcanon, M64. apply Z_mod_plus_full. Qed.

(* row 267..269's length arithmetic: (-p') + 1 + s6 = s6 - p' + 1 *)
Lemma vrd_U_len : forall E (p s : Z), U E (SOff 10 0) = p -> U E (SOff 22 0) = s -> p <= s -> s - p + 1 < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 18446744073709551615)) (SLit 1)) (SOff 22 0))
  = s - p + 1.
Proof.
intros E p s Hp Hs Hps Hlt.
pose proof (U_range E (SOff 10 0)) as Rp. pose proof (U_range E (SOff 22 0)) as Rs. unfold M64 in *.
rewrite !U_SAlu, U_SMd, !U_SLit, Hp, Hs. cbn [zalu_raw zmd_raw].
rewrite (YP0m.zcanon_small 18446744073709551615) by lia.
rewrite vrd_can_add_l, <- Z.add_assoc, vrd_can_add_l.
rewrite (YP0m.zcanon_small 1) by lia.
replace (p * 18446744073709551615 + (1 + s)) with ((s - p + 1) + p * 2 ^ 64) by lia.
rewrite vrd_can_add_mod. apply YP0m.zcanon_small. lia.
Qed.
Lemma vrd_U_len0 : forall E (p s : Z), U E (SOff 10 0) = p -> U E (SOff 22 0) = s -> p <= s -> s - p < 2 ^ 64 ->
  U E (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit (-1))) (SOff 22 0)) = s - p.
Proof.
intros E p s Hp Hs Hps Hlt.
pose proof (U_range E (SOff 10 0)) as Rp. pose proof (U_range E (SOff 22 0)) as Rs. unfold M64 in *.
rewrite !U_SAlu, U_SMd, !U_SLit, Hp, Hs. cbn [zalu_raw zmd_raw].
assert (Hm1 : zcanon (-1) = 18446744073709551615) by (vm_compute; reflexivity).
rewrite Hm1, vrd_can_add_l.
replace (p * 18446744073709551615 + s) with ((s - p) + p * 2 ^ 64) by lia.
rewrite vrd_can_add_mod. apply YP0m.zcanon_small. lia.
Qed.

(* the trivial invariant keeps across any call (the old statements below are the _P lemmas at P := fun _ => True) *)
Lemma vrd_true_call : srr_inv_call segs (fun _ : word -> option byte => True).
Proof. intros m m' _ _. exact I. Qed.

(* ---- SEGMENT 267, rows 267..270 (A 0x86334..0x86340): `sub a0, s6, a0` (a0 = |txt|), `sd a0, 0x18(s1)` (the
   length spilled at sp + 24, which rows 282 and 288 read back), `addi a0, a0, 1` and `jal fuzz_malloc`.
   The call goes through YCbqGcall.aj_call_x_sp against fuzz_malloc's PUBLISHED text, tfuzz_malloc_specX (kit
   PRH_FnAlloc.v blob 95e26ff95e63 :269-307), a premise of this lemma as it is of vrd_num_a_stmt. Its post is
   handed to the continuation VERBATIM at n + 1: the hull use at the call's one event, the NULL transfer (E = []), the
   GRANT transfer (E = [HMal (n + 1 + cf_head)]), the OUTCOME clause and prh_alloc_post. The call's hull budget at that
   event is this lemma's premise, as fuzz_malloc's text takes it. There is no run position at the call: the post's
   transfers quantify the run themselves. (The earlier stand-in H_malloc_rp, the room form with an entry position and a
   bare pair, is RETIRED, not restated.) The continuation runs at row 271 with the allocator's answer in a0. ---- *)
(* the generic-invariant twin of SEGMENT 267 (P with srr_inv_laws for the run, YC1fPx's paj_run_x_inv; srr_inv_call
   across fuzz_malloc, whose published post is an m-form, fpostm = fpost .. (fQmn mem Q), ending with the memnorm
   keep): P of the entry memory and P of the memory at row 271 *)
Lemma vrd_seg_267_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P -> srr_inv_call segs P ->
  forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (sp fr p' n : Z) ch1 Lam peak cnt fail ran most own
    (Q : world segs -> config -> Prop),
  tfuzz_malloc_specX B ARx SK ->
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  P mem ->
  (* the registers rows 267..270 read *)
  getr regs 2 = w64 sp -> getr regs 9 = w64 sp -> getr regs 26 = w64 fr -> getr regs 8 = w64 (spZ regs0) ->
  getr regs 10 = w64 p' -> getr regs 22 = w64 (p' + n) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 -> 0 <= fr -> fr + 32 < 2 ^ 64 ->
  0 <= p' -> 0 <= n -> p' + n < 2 ^ 62 ->
  val_mem segs (rdW W mem) (sp + 16) 8 (fr + 32) ->
  (* the frame facts of the caller's window (LESSON 11; the instance discharges them) *)
  0 <= e -> spZ regs0 - STK_parse_value d <= sp -> sp + 64 <= spZ regs0 + e -> sp + 32 <= spZ regs0 - 16 ->
  (sp - (spZ regs0 + e)) mod 16 = 0 -> 0 <= STK_fuzz_malloc ->
  STK_fuzz_malloc + (spZ regs0 + e - sp) <= STK_parse_value d + e ->
  (* the call's own premises: the chain at the call's sp, the text's room and ledger *)
  achain ly (aview segs (w_H W) mem) sp (spZ regs0) ch1 ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
  (* the rounding mode is 0 at the call (the kit's fpre, FRM0-ENTRY): rows 157..270 run no float instruction *)
  frm_zero (@YK11.fp_csr fx) ->
  room_live_cf S -> prh_malloc_univ B ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  (* the call's hull budget, fuzz_malloc's own premise at its one event *)
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (n + 1 + cf_head)] ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  n + 1 + cf_head < cf_malloc_max -> blocks_bytes S + (n + 1 + cf_head) <= LIVE_MAX ->
  (* the continuation at row 271 *)
  (forall (W2 : world segs) ly2 S2 Hp2 (regs2 : bvmap 5 word) mem2 md2 k1 res,
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly2 S2 Hp2 W2 mem2 md2 (k + k1) -> P mem2 ->
     (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     getr regs2 10 = w64 res ->
     room_live_cf S2 ->
     PresetHullBudget.hull_used S S2 [PresetReqAt.HMal (n + 1 + cf_head)] ->
     (* fuzz_malloc's post at n + 1, verbatim (tfuzz_malloc_specX :285-307) *)
     (res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
        (i : nat) (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] ->
        exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S2) ->
     (res <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
        (i : nat) (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
        PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + 1 + cf_head)] ->
        exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + 1 + cf_head)])%nat H0
          hist' S2) ->
     (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
        (i : nat) (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
        PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + 1 + cf_head)] ->
        PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (n + 1 + cf_head)]) -> cnt <> fail ->
        res <> 0 /\
        exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + 1 + cf_head)])%nat H0
          hist' S2) ->
     prh_alloc_post B (n + 1) ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 ->
     (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK_fuzz_malloc <= a < sp) ->
        ~ (sp + 24 <= a < sp + 32) -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
     val_mem segs (rdW W2 mem2) (sp + 16) 8 (fr + 32) ->
     val_mem segs (rdW W2 mem2) (sp + 24) 8 n ->
     (* THE CALLEE'S OWN JOURNAL (own = []), which IelemE's generic after-call lemmas (VrdIStep.v
        vrd_node_ra_at / vrd_src_at / vrd_home_at / vrd_lam_shadow) ask for: from the call state, whose memory
        memc is this segment's memory outside the slot rows 267..269 wrote, to the state at row 271; and the
        allocator relation AT THE CALL STATE, which vrd_node_ra_at takes for its journal's start *)
     (exists (memc : word -> option byte) (mdc : Model) (kc : Z),
        (forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 24 <= a < sp + 32) ->
           aview segs (w_H W) memc a = aview segs (w_H W) mem a) /\
        AJ STK_fuzz_malloc sp [] ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 kc /\
        ARx ly S Hp W memc mdc) ->
     SRr segs W2 (cfg_at segs (BASE + vrd_row 271) regs2 mem2 md2) Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 267) regs mem md) Q.
Proof.
intros P PLAW PCALL d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md sp fr p' n ch1 Lam peak cnt fail ran most own
  Q HMAL
  HJ HPM R2 R9 R26 R8 R10 R22 Rgp Rtp Hsp Hal Hfr0 Hfr Hp'0 Hn0 Hpn V16 He0 Hlo Hhi Hhi2 Ho16 Hfm0 Hbud
  HCH HROD HFZ0 HROOM HUNIV HSEC HC24 HHB HLED Hmax Hlive HCONT.
pose proof HJ as (HAR & Hly & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & HSTACK & _).
pose proof HSTACK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HP46 : 0 <= (2 : Z) ^ 46) by (apply Z.pow_nonneg; lia).
assert (HP47 : (2 : Z) ^ 46 <= 2 ^ 47) by (apply Z.pow_le_mono_r; lia).
assert (HP64 : (2 : Z) ^ 47 <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
assert (Hspc : alloc_ceiling <= sp) by lia.
assert (Wst : forall o, 24 <= o < 32 -> writable_at segs (rdW W mem) (sp + o))
  by (intros o Ho; apply (apresent_writable segs); apply Hpres; lia).
pose proof (vrd_st_267 W regs mem sp fr R9 R26 Hsp Hal Hfr0 Hfr V16 Wst) as HS.
assert (E9 : ew (vrd_E regs) 9 = getr regs 9)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 9 9%bv eq_refl)).
assert (E10 : ew (vrd_E regs) 10 = getr regs 10)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 10 10%bv eq_refl)).
assert (E22 : ew (vrd_E regs) 22 = getr regs 22)
  by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 22 22%bv eq_refl)).
assert (U10 : U (vrd_E regs) (SOff 10 0) = p')
  by (rewrite U_SOff, E10, R10, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia;
      apply YP0m.zcanon_small; lia).
assert (U22 : U (vrd_E regs) (SOff 22 0) = p' + n)
  by (rewrite U_SOff, E22, R22, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia;
      apply YP0m.zcanon_small; lia).
assert (HEI : img_env VAL A_LIM (vrd_E regs)) by (unfold vrd_E; apply Eimg_env).
assert (SHOK : sh_ok segs vrd_Bx0 (@nil shent) (vrd_E regs) (rdW W mem)) by (apply Forall_nil).
pose (RUN := paj_run_x_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
unfold cfg_at.
paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan0.
- intros a Ha. destruct Ha as (r & Hin & Hr). cbn [vrd_267_regions In] in Hin.
  destruct Hin as [<- | []]. cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr.
  rewrite E9, R9 in Hr. unfold w64 in Hr. rewrite unsigned_lit_small in Hr by lia.
  left. lia.
- (* the state at the call (row 270), the stack slot written, the registers *)
  lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ =>
    assert (KEEP : forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 24 <= a < sp + 32) ->
              aview segs (w_H W) (ms_mem msq) a = aview segs (w_H W) mem a)
  end.
  { intros a Ha64 Ha. unfold aview. f_equal. unfold mbyte.
    rewrite (HFr (Z_to_bv 64 a)); [reflexivity|].
    intros (r & Hin & Hr). cbn [vrd_267_regions In] in Hin. destruct Hin as [<- | []].
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr. rewrite E9, R9 in Hr.
    unfold w64 in Hr. rewrite unsigned_lit_small in Hr by lia.
    rewrite unsigned_lit_small in Hr by exact Ha64. apply Ha. lia. }
  assert (KEEPlo : forall a, 0 <= a < sp + 24 -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha; apply KEEP; lia).
  pose proof (vrd_ledger_hi (sp + 24) ly S Hp W mem (ms_mem ms) mem md Lam peak cnt fail ran most own ltac:(lia) HAR
    HLED KEEPlo) as HLED1.
  assert (KEEProd : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a)
    by (intros a Ha; apply KEEP; lia).
  pose proof (vrd_rod_hi W W mem (ms_mem ms) HROD KEEProd) as HROD1.
  assert (KEEPch : forall a, spZ regs0 - 16 <= a -> a < ly_top ly ->
            aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { intros a Ha Ha2.
    assert (H4764 : (2 : Z) ^ 47 <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite Etop in Ha2. apply KEEP; [split; lia | lia]. }
  pose proof (vrd_achain_hi ly (aview segs (w_H W) mem) (aview segs (w_H W) (ms_mem ms)) sp (spZ regs0) ch1 HCH
                KEEPch) as HCH1.
  prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
  prreg HS (4%bv : bv 5) P4. prreg HS (8%bv : bv 5) P8. prreg HS (10%bv : bv 5) P10.
  assert (E2 : ew (vrd_E regs) 2 = getr regs 2)
    by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E3 : ew (vrd_E regs) 3 = getr regs 3)
    by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 3 3%bv eq_refl)).
  assert (E4 : ew (vrd_E regs) 4 = getr regs 4)
    by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 4 4%bv eq_refl)).
  assert (E8 : ew (vrd_E regs) 8 = getr regs 8)
    by (unfold vrd_E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 8 8%bv eq_refl)).
  assert (Hden1 : sv_denot (vrd_E regs)
            (SAlu ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit 18446744073709551615)) (SLit 1)) (SOff 22 0))
          = w64 (n + 1)).
  { pose proof (vrd_U_len (vrd_E regs) p' (p' + n) U10 U22 ltac:(lia) ltac:(lia)) as HU.
    replace (p' + n - p' + 1) with (n + 1) in HU by lia.
    unfold U in HU. unfold w64. rewrite <- HU. symmetry. apply Z_to_bv_bv_unsigned. }
  assert (Hden0 : sv_denot (vrd_E regs) (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit (-1))) (SOff 22 0)) = w64 n).
  { pose proof (vrd_U_len0 (vrd_E regs) p' (p' + n) U10 U22 ltac:(lia) ltac:(lia)) as HU.
    replace (p' + n - p') with n in HU by lia.
    unfold U in HU. unfold w64. rewrite <- HU. symmetry. apply Z_to_bv_bv_unsigned. }
  pose proof (vrd_val_of_st_ok (vrd_E regs) _ ms _ _ 0%nat HS eq_refl 24
                (SAlu ALU_ADD (SMd M_MUL (SOff 10 0) (SLit (-1))) (SOff 22 0)) n
                ltac:(cbn [vrd_267_regions YP09.r_chunks In]; tauto) Hden0 ltac:(lia)) as XV.
  assert (V24 : val_mem segs (rdW W (ms_mem ms)) (sp + 24) 8 n).
  { cbn [base_val YP09.r_base] in XV. rewrite E9, R9 in XV. unfold w64 in XV.
    rewrite unsigned_lit_small in XV by lia. exact XV. }
  assert (V16' : val_mem segs (rdW W (ms_mem ms)) (sp + 16) 8 (fr + 32)).
  { eapply val_mem_kept; [|exact V16]. intros kk Hk. apply KEEP; lia. }
  assert (HspT : spZ (ms_regs ms) = sp)
    by (unfold spZ; rewrite P2, E2, R2; unfold w64; apply unsigned_lit_small; lia).
  assert (HAE : env_agree 32 (Ereg regs []) (vrd_E regs))
    by (split; [intros nn Hn; unfold vrd_E; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (HPR0 : aregs_preserved regs (ms_regs ms))
    by (eapply (aregs_preserved_of_st_ok segs _ _ _ _ regs (@nil word) HS); [exact HAE | vm_compute; reflexivity]).
  pose proof (pa_base_lo (PL := PL_prog_A) (PI := PI_prog_A)) as HBLO.
  change (@pa_lo _ _ PI_prog_A) with IMG_LO in HBLO. unfold IMG_LO in HBLO.
  pose proof (@pa_B_ok _ _ PI_prog_A) as HBASE.
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ =>
    eapply (aj_call_x_sp (SK := SK) segs B prh_pst ARx LAWS (@pa_segs_low _ _ PI_prog_A)
      W (vrd_E regs) _ msq (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v)
      ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp mdq k STK_fuzz_malloc []
      (sp - (spZ regs0 + e)) _ ch1 _ HS eq_refl HJ) end.
  - rewrite HspT. lia.
  - exact Ho16.
  - lia.
  - exact Hfm0.
  - lia.
  - rewrite P3, E3. exact Rgp.
  - rewrite P4, E4. exact Rtp.
  - exact P1.
  - apply (ret_ok_codeptr_v (PI := PI_prog_A)); [lia | reflexivity].
  - rewrite unsigned_lit_small by lia. lia.
  - replace (spZ regs0 + e + (sp - (spZ regs0 + e))) with sp by lia.
    unfold s0Z. rewrite P8, E8, R8. unfold w64. rewrite unsigned_lit_small by lia. exact HCH1.
  - intros HPRE1.
    (* the live premise is GUARDED in the kit's cut (PRH_FnAlloc.v blob 4d8aeba047e5 :283, cnt <> fail ->): ours holds
       unguarded *)
    refine (HMAL ly S Hp W _ _ _ ch1 (n + 1) Lam peak cnt fail ran most own
              (conj HPRE1 (conj HROD1 (conj _ (conj _ HFZ0)))) HROOM HUNIV HSEC HC24 HHB _ ltac:(lia) ltac:(lia) HLED1
              (fun _ => Hlive)).
    + rewrite HspT. lia.
    + (* fpre's fourth conjunct (record texts 51daa1e80a99): the return address is the jal's own return pc *)
      pose proof asan_consts as (AC1 & _). unfold raZ. rewrite P1.
      assert (EB : VAL A_TEXT = 529888) by (vm_compute; reflexivity).
      rewrite EB. rewrite unsigned_lit_small by lia. lia.
    + rewrite P10. cbn [sv_denot] in Hden1.
      rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned in Hden1. exact Hden1.
  - intros a (r & Hr & _). destruct Hr. }
  cbv beta. intros W2 c2 _
    (ly2 & S2 & Hp2 & regs3 & mem3 & md3 & k1 & -> & HJ3 & HJc & HPR3 &
     (res & Hres & HRK2 & HHUL & HT0 & HT1 & HOC & HAP) & HMN).
  (* fuzz_malloc's post (the kit's cut, PRH_FnAlloc.v blob 4d8aeba047e5 :285-310) READ BY ITS CONJUNCTS' TYPES: each name
     is checked against the text's spelling here, so a conjunct the text gains fails at this line, loudly, instead of
     binding the wrong conjunct (the internal file MIGRATION.md section 3) *)
  change (getr regs3 10 = w64 res) in Hres. change (room_live_cf S2) in HRK2.
  change (PresetHullBudget.hull_used S S2 [PresetReqAt.HMal (n + 1 + cf_head)]) in HHUL.
  change (res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
            (i : nat) (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] ->
            exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S2)
    in HT0.
  change (res <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
            (i : nat) (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
            PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + 1 + cf_head)] ->
            exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + 1 + cf_head)])%nat
              H0 hist' S2) in HT1.
  change (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
            (i : nat) (H0 : list Z) (hist : list YG00.chunk),
            PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
            PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + 1 + cf_head)] ->
            PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (n + 1 + cf_head)]) -> cnt <> fail ->
            res <> 0 /\
            exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + 1 + cf_head)])%nat
              H0 hist' S2) in HOC.
  change (prh_alloc_post B (n + 1) ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem3) in HAP.
  pose proof HJc as (_ & _ & _ & _ & _ & _ & _ & _ & GC & _).
  replace (spZ regs0 + e + (sp - (spZ regs0 + e))) with sp in GC by lia.
  assert (KEEPc : forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK_fuzz_malloc <= a < sp) ->
            aview segs (w_H W2) mem3 a = aview segs (w_H W) (ms_mem ms) a)
    by (intros a Ha Hn; exact (GC a Ha Hn)).
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq ?pcq ?mq _) ?dq) _ =>
    replace (mkCfg (mkst rq pcq mq (seg_rom segs)) dq)
      with (cfg_at segs (BASE + vrd_row 271) rq mq dq)
      by (unfold cfg_at, w64; repeat f_equal; vm_compute; reflexivity) end.
  apply (HCONT W2 ly2 S2 Hp2 regs3 mem3 md3 k1 res HJ3 (PCALL _ _ HMN HPM)).
  { intros r Hr. rewrite (HPR3 r Hr). exact (HPR0 r Hr). }
  { exact Hres. }
  { exact HRK2. }
  { exact HHUL. }
  { exact HT0. }
  { exact HT1. }
  { exact HOC. }
  { exact HAP. }
  { intros a Ha Hn1 Hn2. rewrite (KEEPc a Ha Hn1). apply KEEP; [split; lia | lia]. }
  { eapply val_mem_kept; [|exact V16']. intros kk Hk. apply KEEPc; [split; lia | lia]. }
  { eapply val_mem_kept; [|exact V24]. intros kk Hk. apply KEEPc; [split; lia | lia]. }
  { exists (ms_mem ms). do 2 eexists. split; [|split].
    - intros a Ha64 Ha. apply KEEP; [exact Ha64 | exact Ha].
    - replace sp with (spZ regs0 + e + (sp - (spZ regs0 + e))) by lia. exact HJc.
    - exact (proj1 HJ). }
Qed.

(* the old statement, byte-identical: vrd_seg_267_P at P := fun _ => True *)
Lemma vrd_seg_267 : forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (sp fr p' n : Z) ch1 Lam peak cnt fail ran most own
    (Q : world segs -> config -> Prop),
  tfuzz_malloc_specX B ARx SK ->
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  (* the registers rows 267..270 read *)
  getr regs 2 = w64 sp -> getr regs 9 = w64 sp -> getr regs 26 = w64 fr -> getr regs 8 = w64 (spZ regs0) ->
  getr regs 10 = w64 p' -> getr regs 22 = w64 (p' + n) ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 -> 0 <= fr -> fr + 32 < 2 ^ 64 ->
  0 <= p' -> 0 <= n -> p' + n < 2 ^ 62 ->
  val_mem segs (rdW W mem) (sp + 16) 8 (fr + 32) ->
  (* the frame facts of the caller's window (LESSON 11; the instance discharges them) *)
  0 <= e -> spZ regs0 - STK_parse_value d <= sp -> sp + 64 <= spZ regs0 + e -> sp + 32 <= spZ regs0 - 16 ->
  (sp - (spZ regs0 + e)) mod 16 = 0 -> 0 <= STK_fuzz_malloc ->
  STK_fuzz_malloc + (spZ regs0 + e - sp) <= STK_parse_value d + e ->
  (* the call's own premises: the chain at the call's sp, the text's room and ledger *)
  achain ly (aview segs (w_H W) mem) sp (spZ regs0) ch1 ->
  arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem) ->
  (* the rounding mode is 0 at the call (the kit's fpre, FRM0-ENTRY): rows 157..270 run no float instruction *)
  frm_zero (@YK11.fp_csr fx) ->
  room_live_cf S -> prh_malloc_univ B ->
  YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV ->
  YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV ->
  PresetHullBudget.hull_budget S [PresetReqAt.HMal (n + 1 + cf_head)] ->
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  n + 1 + cf_head < cf_malloc_max -> blocks_bytes S + (n + 1 + cf_head) <= LIVE_MAX ->
  (* the continuation at row 271 *)
  (forall (W2 : world segs) ly2 S2 Hp2 (regs2 : bvmap 5 word) mem2 md2 k1 res,
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly2 S2 Hp2 W2 mem2 md2 (k + k1) ->
     (forall r, acallee_saved r -> getr regs2 (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
     getr regs2 10 = w64 res ->
     room_live_cf S2 ->
     PresetHullBudget.hull_used S S2 [PresetReqAt.HMal (n + 1 + cf_head)] ->
     (* fuzz_malloc's post at n + 1, verbatim (tfuzz_malloc_specX :285-307) *)
     (res = 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
        (i : nat) (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S -> PRH_Base.prh_run_at sm x os i [] ->
        exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S2) ->
     (res <> 0 -> forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
        (i : nat) (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
        PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + 1 + cf_head)] ->
        exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + 1 + cf_head)])%nat H0
          hist' S2) ->
     (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
        (i : nat) (H0 : list Z) (hist : list YG00.chunk),
        PresetRoomPos.iface_room_pos sm x os i H0 hist S ->
        PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (n + 1 + cf_head)] ->
        PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (n + 1 + cf_head)]) -> cnt <> fail ->
        res <> 0 /\
        exists hist', PresetRoomPos.iface_room_pos sm x os (i + length [PresetReqAt.HMal (n + 1 + cf_head)])%nat H0
          hist' S2) ->
     prh_alloc_post B (n + 1) ly S Hp W Lam peak cnt fail ran most own res ly2 S2 Hp2 W2 mem2 ->
     (forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp - STK_fuzz_malloc <= a < sp) ->
        ~ (sp + 24 <= a < sp + 32) -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem a) ->
     val_mem segs (rdW W2 mem2) (sp + 16) 8 (fr + 32) ->
     val_mem segs (rdW W2 mem2) (sp + 24) 8 n ->
     (* THE CALLEE'S OWN JOURNAL (own = []), which IelemE's generic after-call lemmas (VrdIStep.v
        vrd_node_ra_at / vrd_src_at / vrd_home_at / vrd_lam_shadow) ask for: from the call state, whose memory
        memc is this segment's memory outside the slot rows 267..269 wrote, to the state at row 271; and the
        allocator relation AT THE CALL STATE, which vrd_node_ra_at takes for its journal's start *)
     (exists (memc : word -> option byte) (mdc : Model) (kc : Z),
        (forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 24 <= a < sp + 32) ->
           aview segs (w_H W) memc a = aview segs (w_H W) mem a) /\
        AJ STK_fuzz_malloc sp [] ly S Hp W memc mdc [] ly2 S2 Hp2 W2 mem2 md2 kc /\
        ARx ly S Hp W memc mdc) ->
     SRr segs W2 (cfg_at segs (BASE + vrd_row 271) regs2 mem2 md2) Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 267) regs mem md) Q.
Proof.
intros d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md sp fr p' n ch1 Lam peak cnt fail ran most own
  Q HMAL
  HJ R2 R9 R26 R8 R10 R22 Rgp Rtp Hsp Hal Hfr0 Hfr Hp'0 Hn0 Hpn V16 He0 Hlo Hhi Hhi2 Ho16 Hfm0 Hbud
  HCH HROD HFZ0 HROOM HUNIV HSEC HC24 HHB HLED Hmax Hlive HCONT.
exact (vrd_seg_267_P (fun _ => True) (srr_inv_laws_true segs) vrd_true_call d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos
  ly S Hp k W regs mem md sp fr p' n ch1 Lam peak cnt fail ran most own Q HMAL
  HJ I R2 R9 R26 R8 R10 R22 Rgp Rtp Hsp Hal Hfr0 Hfr Hp'0 Hn0 Hpn V16 He0 Hlo Hhi Hhi2 Ho16 Hfm0 Hbud
  HCH HROD HFZ0 HROOM HUNIV HSEC HC24 HHB HLED Hmax Hlive
  (fun W2 ly2 S2 Hp2 regs2 mem2 md2 k1 res HJ2 _ => HCONT W2 ly2 S2 Hp2 regs2 mem2 md2 k1 res HJ2)).
Qed.

(* ======================================================================================================== *)
(* ROWS 271..283: the node's str word, the NULL test, the shadow of the cursor and the memcpy                   *)
(* ======================================================================================================== *)

(* the registers rows 271..328 never write: every callee-saved register but s9 (rows 271 and 296 set it); s5 is set
   at row 324 only, after the last exit that states this predicate *)
Definition vrd_tk (regs' regs : bvmap 5 word) : Prop :=
  forall r, acallee_saved r -> r <> 25 -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r).
Definition vrd_tk_l : list (bv 5) := map (Z_to_bv 5) [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 26].
Lemma vrd_cs_split : forall r, acallee_saved r -> r <> 25 -> r = 27 \/ In (Z_to_bv 5 r) vrd_tk_l.
Proof.
intros r Hr H25. unfold acallee_saved in Hr.
assert (Hc : r = 2 \/ r = 3 \/ r = 4 \/ r = 8 \/ r = 9 \/ r = 18 \/ r = 19 \/ r = 20 \/ r = 21 \/ r = 22 \/
             r = 23 \/ r = 24 \/ r = 26 \/ r = 27) by lia.
destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]]]]]]];
  first [left; reflexivity | right; unfold vrd_tk_l; apply in_map; cbn [In]; tauto].
Qed.
Lemma vrd_tk_trans : forall r3 r2 r1, vrd_tk r3 r2 -> vrd_tk r2 r1 -> vrd_tk r3 r1.
Proof. intros r3 r2 r1 H32 H21 r Hr H25. rewrite (H32 r Hr H25). exact (H21 r Hr H25). Qed.
Lemma vrd_tk_pres : forall r2 r1, aregs_preserved r1 r2 -> vrd_tk r2 r1.
Proof. intros r2 r1 HP r Hr _. exact (HP r Hr). Qed.

(* shadow_addr (atom m + o), as the engine's shadow-token match reads it (YCbn.match_x: (x >> 3) + Bx, Bx = s7);
   s11 = shadow_addr q is pinned to it so that rows 279 and 322 resolve *)
Definition vrd_shx (m : nat) (o : Z) : sv := SAlu ALU_ADD (SAlu ALU_SRL (SOff m o) (SLit 3)) (SOff 23 0).
Definition vrd_shq : sv := vrd_shx 20 0.

Lemma vrd_U_shx : forall E m o x, U E (SOff m o) = x -> U E (SOff 23 0) = SHADOW_OFF -> 0 <= x < 2 ^ 64 ->
  U E (vrd_shx m o) = SHADOW_OFF + x / 8.
Proof.
intros E m o x Hq Hb Hr. unfold vrd_shx. rewrite !U_SAlu, U_SLit, Hq, Hb. cbn [zalu_raw].
rewrite (YP0m.zcanon_small 3) by lia. change (Z.land 3 63) with 3.
rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as H0.
assert (H1 : x / 8 < 2 ^ 61) by (apply Z.div_lt_upper_bound; lia).
rewrite (YP0m.zcanon_small (x / 8)) by lia. rewrite Z.add_comm. apply YP0m.zcanon_small. unfold SHADOW_OFF. lia.
Qed.

(* the shadow band: the shadow bytes of the low 2 ^ 47 addresses *)
Lemma vrd_sh_band : forall x, 0 <= x < 2 ^ 47 -> SHADOW_OFF <= shadow_of_addr SHADOW_OFF x < kHighShadowEnd.
Proof.
intros x Hx. unfold shadow_of_addr, SHADOW_OFF, kHighShadowEnd.
pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)) as H0.
assert (H1 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia). lia.
Qed.

(* addressability and the visible hull survive any change off the shadow band *)
Lemma vrd_ra_shkeep : forall (H H' : word -> bool) (m m' : word -> option byte) a n,
  0 <= a -> a + n <= 2 ^ 47 ->
  (forall s, SHADOW_OFF <= s < kHighShadowEnd -> aview segs H' m' s = aview segs H m s) ->
  range_addressable (aview segs H m) SHADOW_OFF a n -> range_addressable (aview segs H' m') SHADOW_OFF a n.
Proof.
intros H H' m m' a n Ha Hn HK HR x Hx. destruct (HR x Hx) as (s & Hs & Ho). exists s. split; [|exact Ho].
rewrite HK; [exact Hs | apply vrd_sh_band; lia].
Qed.
Lemma vrd_hull_shkeep : forall (H H' : word -> bool) (m m' : word -> option byte) a n,
  0 <= a -> 0 < n -> a + n <= 2 ^ 47 - 64 ->
  (forall s, SHADOW_OFF <= s < kHighShadowEnd -> aview segs H' m' s = aview segs H m s) ->
  shadow_hull_vis (aview segs H m) a n -> shadow_hull_vis (aview segs H' m') a n.
Proof.
intros H H' m m' a n Ha Hn Hn2 HK HV s Hs. rewrite HK; [exact (HV s Hs)|].
unfold shadow_addr in Hs. unfold SHADOW_OFF in *. unfold kHighShadowEnd.
replace (2147450880 + a / 8) with (268431360 * 8 + a / 8) in Hs by lia.
rewrite Z.div_add_l in Hs by lia.
pose proof (Z.div_pos a 8 ltac:(lia) ltac:(lia)) as H0.
pose proof (Z.div_pos (a / 8) 8 ltac:(lia) ltac:(lia)) as H1.
pose proof (Z.mul_div_le (2147450880 + (a + n - 1) / 8) 8 ltac:(lia)) as H2.
assert (H3 : (a + n - 1) / 8 < 2 ^ 44 - 8) by (apply Z.div_lt_upper_bound; lia).
lia.
Qed.

(* a run's frame keeps the reader view off its write windows *)
Lemma vrd_fr_aview : forall E rs (H : word -> bool) (m m' : word -> option byte) a,
  frame_of E rs (mrestrict H m) (mrestrict H m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  aview segs H m' a = aview segs H m a.
Proof.
intros E rs H m m' a HF Ha Hn. unfold aview. f_equal. unfold mbyte.
rewrite (HF (Z_to_bv 64 a)); [reflexivity|]. rewrite unsigned_lit_small by lia. exact Hn.
Qed.

(* presence growth in the two forms the engine and the call rules give it *)
Lemma vrd_mg_of_pres : forall (H : word -> bool) (m m' : word -> option byte),
  (forall a, apresent H m a -> apresent H m' a) -> mem_grows (mrestrict H m) (mrestrict H m').
Proof.
intros H m m' HP x Hx. unfold mrestrict in *. destruct (H x) eqn:Hh; [exfalso; exact (Hx eq_refl)|].
destruct (m x) as [b|] eqn:Hm; [|exfalso; exact (Hx eq_refl)].
assert (Ha : apresent H m (bv_unsigned x)) by (split; rewrite Z_to_bv_bv_unsigned; [exact Hh | exists b; exact Hm]).
destruct (HP _ Ha) as [_ (b' & Hb')]. rewrite Z_to_bv_bv_unsigned in Hb'. rewrite Hb'. discriminate.
Qed.
Lemma vrd_pres_of_mg : forall (H : word -> bool) (m m' : word -> option byte) a,
  mem_grows (mrestrict H m) (mrestrict H m') -> apresent H m a -> apresent H m' a.
Proof.
intros H m m' a HG [Hh (b & Hb)]. split; [exact Hh|]. specialize (HG (Z_to_bv 64 a)).
unfold mrestrict in HG. rewrite Hh, Hb in HG. destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity|].
exfalso. exact (HG ltac:(discriminate) eq_refl).
Qed.

(* ---- the state at row 271 (A 0x86344), after the allocator returned (a0 = res): the stack slots [sp, sp + 32)
   (writable [sp + 8, sp + 16), the endptr cell's address fr + 32 at sp + 16 and the length n at sp + 24), the
   node's str word [v + 16, v + 24) (writable), the cursor's p word [q, q + 8) holding p'; s11 is pinned to the
   shadow address of q. The two shadow entries make rows 274 and 279's shadow loads resolve to 0, and the first
   covers the node's write window (cells_safe_b). Extra atoms: 32 = n, 33 = p'. Measured
   by symbolic execution: row 277 stops on `beqz a0`; taken it reaches row 326, not taken it stops at the
   call of __asan_memcpy (row 283); sh_obls = [] on every run. ---- *)
Definition vrd_271_sr : list sv := sr_set sr_atoms 27%bv vrd_shq.
Definition vrd_271_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 0 32 8 16
      [YP09.mkChunk 16 (CVal 8 (SOff 26 32)); YP09.mkChunk 24 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 19%nat) 16 24 16 24 [];
    YP09.mkRegion (Some 20%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 33 0))] ].
Definition vrd_271_facts : facts := mkFacts
  [ (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 5); (19%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0);
    (20%nat, mkAF 4096 (2 ^ 47 - 24) 0); (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0) ] [] [].
Definition ss_vrd_271 : sstate := mkSS (vrd_row 271) vrd_271_sr vrd_271_regions None vrd_271_facts.
Definition vrd_SH271 : list shent := [mkSHE 19 16 24; mkSHE 20 0 8].

Lemma vrd_st_271 : forall (W : world segs) regs mem (sp fr v q n p' : Z),
  getr regs 9 = w64 sp -> getr regs 26 = w64 fr -> getr regs 19 = w64 v -> getr regs 20 = w64 q ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 (SHADOW_OFF + q / 8) ->
  2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 -> 0 <= fr -> fr + 32 < 2 ^ 64 ->
  4096 <= v -> v + 24 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= q -> q + 24 <= 2 ^ 47 ->
  0 <= n < 2 ^ 64 -> 0 <= p' < 2 ^ 64 ->
  (v + 24 <= sp \/ sp + 32 <= v + 16) -> (q + 8 <= sp \/ sp + 32 <= q) -> (v + 24 <= q \/ q + 8 <= v + 16) ->
  val_mem segs (rdW W mem) (sp + 16) 8 (fr + 32) -> val_mem segs (rdW W mem) (sp + 24) 8 n ->
  val_mem segs (rdW W mem) q 8 p' ->
  (forall o, 8 <= o < 16 -> writable_at segs (rdW W mem) (sp + o)) ->
  (forall o, 16 <= o < 24 -> writable_at segs (rdW W mem) (v + o)) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (v + 16) 8 -> amem_range (v + 16) 8 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 8 -> amem_range q 8 ->
  st_ok_pi segs VAL (vrd_E2 regs n p') ss_vrd_271
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row 271)) mem (seg_rom segs))) /\
  sh_ok segs vrd_Bx vrd_SH271 (vrd_E2 regs n p') (rdW W mem).
Proof.
intros W regs mem sp fr v q n p' R9 R26 R19 R20 R23 R27 Hsp Hal Hfr0 Hfr Hv0 Hv1 Hq0 Hq1 Hn Hp
  Dsv Dsq Dvq V16 V24 Vq Wst Wnd RAv Amv RAq Amq.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (EL : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew (vrd_E2 regs n p') m = getr regs r)
  by (intros m r Hm Hr; unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ m r Hr)).
assert (E32 : ew (vrd_E2 regs n p') 32 = w64 n)
  by (unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew (vrd_E2 regs n p') 33 = w64 p')
  by (unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (U9 : bv_unsigned (ew (vrd_E2 regs n p') 9) = sp)
  by (rewrite (EL 9%nat 9%bv) by (lia || reflexivity); rewrite R9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew (vrd_E2 regs n p') 19) = v)
  by (rewrite (EL 19%nat 19%bv) by (lia || reflexivity); rewrite R19; apply unsigned_lit_small; lia).
assert (U20 : bv_unsigned (ew (vrd_E2 regs n p') 20) = q)
  by (rewrite (EL 20%nat 20%bv) by (lia || reflexivity); rewrite R20; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew (vrd_E2 regs n p') 23) = SHADOW_OFF)
  by (rewrite (EL 23%nat 23%bv) by (lia || reflexivity); rewrite R23; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U26 : bv_unsigned (ew (vrd_E2 regs n p') 26) = fr)
  by (rewrite (EL 26%nat 26%bv) by (lia || reflexivity); rewrite R26; apply unsigned_lit_small; lia).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold vrd_271_sr. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate |].
    rewrite R27. symmetry. apply vrd_sv_eq. apply (vrd_U_shx _ 20 0).
    * rewrite U_SOff, U20, Z.add_0_r. apply YP0m.zcanon_small. lia.
    * rewrite U_SOff, U23, Z.add_0_r. apply YP0m.zcanon_small. lia.
    * lia.
  + vm_compute. reflexivity.
  + unfold vrd_271_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Wst o Ho)|].
      repeat constructor.
      -- apply (chunk_ok_val segs _ _ sp 16 8 (SOff 26 32) (fr + 32));
           [apply vrd_sv_eq; rewrite U_SOff, U26; apply YP0m.zcanon_small; lia | cbn; lia | lia | exact V16].
      -- apply (chunk_ok_val segs _ _ sp 24 8 (SOff 32 0) n);
           [cbn [sv_denot]; rewrite E32, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
           | cbn; lia | lia | exact V24].
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; exact (Wnd o Ho) | constructor].
    * rewrite U20. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat constructor.
      apply (chunk_ok_val segs _ _ q 0 8 (SOff 33 0) p');
        [cbn [sv_denot]; rewrite E33, Z.add_0_r; unfold w64; rewrite Z_to_bv_bv_unsigned; reflexivity
        | cbn; lia | lia | rewrite Z.add_0_r; exact Vq].
  + apply pairwise_disjoint_of_extents. unfold vrd_271_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
    rewrite U9, U19, U20. unfold zdisj. cbn [fst snd]. repeat split; first [lia | left; lia | right; lia].
  + split; [|split; [exact I | exact I]].
    cbn [vrd_271_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U20, U23. change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
    repeat split; try lia; try exact I.
- unfold sh_ok, vrd_SH271. repeat (apply Forall_cons); try apply Forall_nil.
  + apply (shent_ok_of_range segs (w_H W) mem _ vrd_Bx 19 (v + 16) 8 v 16 24 RAv).
    * unfold vrd_Bx. rewrite YP0e.U_SOff, U23, Z.add_0_r. apply YP0m.zcanon_small. lia.
    * rewrite YP0e.U_SOff, U19, Z.add_0_r. apply YP0m.zcanon_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amv. lia.
  + apply (shent_ok_of_range segs (w_H W) mem _ vrd_Bx 20 q 8 q 0 8 RAq).
    * unfold vrd_Bx. rewrite YP0e.U_SOff, U23, Z.add_0_r. apply YP0m.zcanon_small. lia.
    * rewrite YP0e.U_SOff, U20, Z.add_0_r. apply YP0m.zcanon_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amq. lia.
Qed.

(* a value a chunk of the symbolic state holds, at an address given by its region base and offset *)
Lemma vrd_val_at : forall E ss ms (H : word -> bool) b lo hi wlo whi cs off (n : N) ev v a,
  st_ok_pi segs VAL E ss (restrict H ms) ->
  In (YP09.mkRegion b lo hi wlo whi cs) (ss_mem ss) -> In (YP09.mkChunk off (CVal n ev)) cs ->
  base_val E b + off = a -> sv_denot E ev = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem segs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof. intros E ss ms H b lo hi wlo whi cs off n ev v a HS Hr Hc <-. exact (vrd_val_of_st E ss ms H b lo hi wlo whi cs off n ev v HS Hr Hc). Qed.
Lemma vrd_val_at_ok : forall E ss ms (H : word -> bool) b lo hi wlo whi cs off (n : N) ev v a,
  st_ok segs E ss (restrict H ms) ->
  In (YP09.mkRegion b lo hi wlo whi cs) (ss_mem ss) -> In (YP09.mkChunk off (CVal n ev)) cs ->
  base_val E b + off = a -> sv_denot E ev = Z_to_bv 64 v -> 0 <= v < 2 ^ (8 * Z.of_N n) -> Z.of_N n <= 8 ->
  val_mem segs (mrestrict H (ms_mem ms)) a (N.to_nat n) v.
Proof.
intros E ss ms H b lo hi wlo whi cs off n ev v a HS Hr Hc <- He Hv Hn.
destruct HS as (_ & _ & _ & _ & _ & _ & _ & HM & _).
apply (val_of_chunk_ok segs E _ _ off n ev v); [|exact He|exact Hv|exact Hn].
apply (region_ok_chunk segs E _ (YP09.mkRegion b lo hi wlo whi cs)); [|exact Hc].
eapply mem_ok_region; [exact HM | exact Hr].
Qed.

(* ---- the walk's tactics (VrdNum.v's are Local there; these take every hypothesis as a parameter) ----
   vrd_rl: compute a region list in an In hypothesis; vrd_valg: a chunk's value as a val_mem goal; vrd_keep: a byte
   off every write window is unchanged across every run so far (each run's frame_of, chained); vrd_grow: presence
   grows across every run so far; vrd_regv / vrd_q27 / vrd_tkr: registers after a run or at a call. *)
Local Ltac vrd_rl Hin :=
  lazymatch type of Hin with In _ ?l => let l' := eval vm_compute in l in change l with l' in Hin end;
  cbn [In] in Hin.
Local Ltac vrd_inw U9 U19 :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vrd_rl Hin; repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U19 in Hr; lia.
Local Ltac vrd_keep U9 U19 Ha64 :=
  repeat match goal with
  | HFx : frame_of _ ?rs (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2) |- aview _ ?Hh ?m2 ?a = _ =>
      transitivity (aview segs Hh m1 a);
      [ apply (vrd_fr_aview _ rs Hh m1 m2 a HFx Ha64); vrd_inw U9 U19 | clear HFx ]
  end; reflexivity.
Local Ltac vrd_grow :=
  repeat match goal with
  | HGx : mem_grows (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2) |- mem_grows (mrestrict ?Hh ?m0) (mrestrict ?Hh ?m2) =>
      apply (vrd_mg_trans _ (mrestrict Hh m1)); [clear HGx | exact HGx]
  end; apply mem_grows_refl.
Local Ltac vrd_valg HS bnat off :=
  let go EE ssq :=
    let l := eval vm_compute in (ss_mem ssq) in
    lazymatch l with context [YP09.mkRegion (Some bnat) ?lo ?hi ?wlo ?whi ?cs] =>
      lazymatch cs with context [YP09.mkChunk off (CVal ?nn ?ev)] =>
        first [ eapply (vrd_val_at EE ssq _ _ (Some bnat) lo hi wlo whi cs off nn ev _ _ HS)
              | eapply (vrd_val_at_ok EE ssq _ _ (Some bnat) lo hi wlo whi cs off nn ev _ _ HS) ];
        [ change (ss_mem ssq) with l; cbn [In]; repeat (first [left; reflexivity | right])
        | cbn [In]; repeat (first [left; reflexivity | right])
        | .. ]
      end end in
  lazymatch type of HS with
  | st_ok_pi _ _ ?EE ?ssq _ => go EE ssq
  | st_ok _ ?EE ?ssq _ => go EE ssq
  end.
Local Ltac vrd_regv HS r ev val Hu :=
  let Q := fresh "Q" in
  first [ pose proof (st_ok_pi_restrict_reg _ _ _ _ r HS) as Q
        | pose proof (st_ok_restrict_reg segs _ _ _ _ r HS) as Q ];
  lazymatch type of Q with _ = sv_denot _ ?t => replace t with ev in Q by (vm_compute; reflexivity) end;
  rewrite (vrd_sv_eq _ ev val Hu) in Q; exact Q.
Local Ltac vrd_q27 HS U20 U23 R27 Hq :=
  let Q := fresh "Q27" in
  first [ pose proof (st_ok_pi_restrict_reg _ _ _ _ (Z_to_bv 5 27) HS) as Q
        | pose proof (st_ok_restrict_reg segs _ _ _ _ (Z_to_bv 5 27) HS) as Q ];
  lazymatch type of Q with _ = sv_denot _ ?t => replace t with vrd_shq in Q by (vm_compute; reflexivity) end;
  rewrite (vrd_sv_eq _ vrd_shq _ (vrd_U_shx _ 20 0 _ U20 U23 Hq)) in Q;
  rewrite Q; replace (Z_to_bv 5 27) with (27%bv : bv 5) by (apply bv_eq; reflexivity); rewrite R27; reflexivity.
Local Ltac vrd_tkr HS HAE U20 U23 R27 Hq :=
  let r := fresh "r" in let Hr := fresh "Hr" in let H25 := fresh "H25" in let Hin := fresh "Hin" in
  intros r Hr H25; destruct (vrd_cs_split r Hr H25) as [-> | Hin];
  [ vrd_q27 HS U20 U23 R27 Hq
  | first [ exact (regs_kept_of_st_ok_pi _ _ _ _ _ vrd_tk_l HS HAE ltac:(vm_compute; reflexivity) _ Hin)
          | exact (regs_kept_of_st_ok segs _ _ _ _ _ vrd_tk_l HS HAE ltac:(vm_compute; reflexivity) _ Hin) ] ].

(* STAND-IN (owner: the kit text YGcallMxmn.aintrin_realizes_xm at OCpy, YGcallMx.aintrin_realizes_x with the memnorm
   keep as its last post conjunct; preset's row is a Theorem Labs lane's lib/A/PRowCpy.v prow_asan_memcpy_xm_A, which the
   instance cites at __asan_memcpy, as lib/A/Prog/S6ImgWit.v s6w_aim cites the memset row): __asan_memcpy, as the
   call of row 283 enters it *)
Hypothesis H_checked_memcpy_xm : aintrin_realizes_xm segs B ARx OCpy (pa_sigma AS___asan_memcpy).

(* lia over the arithmetic facts only (VrdArmStrOk.v's slia, a Theorem Labs lane's A'Str lane, verbatim). Measured here: in the
   generic-invariant twin of segment 271, after the second run, each plain lia fell back from the context pruning to
   the full context and took 60-580 s (VrdNumTail.vo 1558 s against 160 s without the twin). slia first clears every
   hypothesis that is not an equation, an order fact or a propositional combination of them; it is used only where
   lia closes the goal (or inside `first`, which undoes the clearing on failure). *)
Local Ltac slia_clear :=
  repeat match goal with
  | H : ?T |- _ =>
      lazymatch type of T with Prop => idtac | _ => fail end;
      lazymatch T with
      | @eq _ _ _ => fail | Z.le _ _ => fail | Z.lt _ _ => fail | Z.ge _ _ => fail | Z.gt _ _ => fail
      | le _ _ => fail | lt _ _ => fail | ge _ _ => fail | gt _ _ => fail
      | _ /\ _ => fail | _ \/ _ => fail | ~ _ => fail | _ <> _ => fail
      | _ => clear H
      end
  end.
Local Ltac slia := slia_clear; lia.

(* ---- SEGMENT 271, rows 271..283 (A 0x86344..0x86374) and the call of __asan_memcpy. Rows 271..276: the shadow of
   the node's str word v + 16 (through s7; it reads 0) and `sd a0, 0(s9)`, the block into the node; row 277
   `beqz a0`: the NULL block goes to the refusal join at row 326 (s5 is still -1); rows 278..283: the shadow
   address of v + 16 spilled at sp + 8, the shadow of the cursor (through s11; 0), a1 = q->p = p', a2 = n from
   sp + 24, and the memcpy (YGcallMxmn.aj_intrin_at_xm at H_checked_memcpy_xm) of the n token bytes into the block. The
   node write runs with YC80xf.paj_run_xf (write premise awr_ok_fr: the node is a caller's live fake frame or a
   block or the caller window). ---- *)
(* the generic-invariant twin of SEGMENT 271 (P with srr_inv_laws for the runs, YC80xf_inv's paj_run_xf_inv /
   paj_run_to_xf_inv; srr_inv_call across __asan_memcpy, whose post through YGcallMxmn.aj_intrin_at_xm ends with
   the memnorm keep): P of the entry memory and P of each exit's memory *)
Lemma vrd_seg_271_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P -> srr_inv_call segs P ->
  forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (sp fr p' n res : Z) (Q : world segs -> config -> Prop),
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  P mem ->
  getr regs 2 = w64 sp -> getr regs 9 = w64 sp -> getr regs 19 = w64 v -> getr regs 20 = w64 q ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 (SHADOW_OFF + q / 8) -> getr regs 26 = w64 fr ->
  getr regs 10 = w64 res -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 -> 0 <= fr -> fr + 32 < 2 ^ 64 ->
  4096 <= v -> v + 24 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= q -> q + 24 <= 2 ^ 47 ->
  0 <= res < 2 ^ 64 -> 0 <= n < 2 ^ 32 -> 0 <= p' < 2 ^ 64 ->
  (v + 24 <= sp - ESTACK \/ sp + 32 <= v + 16) -> (q + 8 <= sp - ESTACK \/ sp + 32 <= q) ->
  (v + 24 <= q \/ q + 8 <= v + 16) ->
  (* the frame facts of the caller's window (the instance discharges them, as for vrd_seg_267) *)
  0 <= e -> spZ regs0 - STK_parse_value d <= sp -> sp + 32 <= spZ regs0 + e ->
  (sp - (spZ regs0 + e)) mod 16 = 0 -> ESTACK + (spZ regs0 + e - sp) <= STK_parse_value d + e ->
  val_mem segs (rdW W mem) (sp + 16) 8 (fr + 32) -> val_mem segs (rdW W mem) (sp + 24) 8 n ->
  val_mem segs (rdW W mem) q 8 p' ->
  (* the node's str word may be written (prhPv_node's home: a block, a caller's live fake frame, the window) *)
  (forall a, v + 16 <= a < v + 24 ->
     awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly S) ly
       [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly a) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 24 -> amem_range v 24 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 8 -> amem_range q 8 ->
  (* the memcpy's premises, when the block is not NULL (prh_alloc_post's success arm; the token in the text) *)
  (res <> 0 ->
     res + n + 1 <= alloc_ceiling /\
     (forall a, res <= a < res + n + 1 -> in_tmp_block (ablocks B ly0 S0) (ablocks B ly S) a) /\
     amem_range res (n + 1) /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF res (n + 1) /\
     (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) res n) /\
     (v + 24 <= res \/ res + n + 1 <= v + 16) /\
     p' + n <= alloc_ceiling /\ (p' + n <= v + 16 \/ v + 24 <= p') /\ (res + n <= p' \/ p' + n <= res) /\
     (forall a, p' <= a < p' + n -> aview segs (w_H W) mem a <> None) /\ amem_range p' n /\
     range_addressable (aview segs (w_H W) mem) SHADOW_OFF p' n /\
     (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) p' n)) ->
  (* row 326: the NULL block, stored in the node *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k -> P mem' ->
     vrd_tk regs' regs -> getr regs' (Z_to_bv 5 25) = w64 (v + 16) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) -> ~ (sp + 8 <= a < sp + 16) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     val_mem segs (rdW W mem') (v + 16) 8 0 -> res = 0 ->
     SRr segs W (cfg_at segs (BASE + vrd_row 326) regs' mem' md') Q) ->
  (* row 284: the block in the node, the token copied into it *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k -> P mem' ->
     vrd_tk regs' regs -> getr regs' (Z_to_bv 5 25) = w64 (v + 16) -> getr regs' 10 = w64 res ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) -> ~ (sp + 8 <= a < sp + 16) ->
        ~ (res <= a < res + n) -> ~ (sp - ESTACK <= a < sp) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     (forall i, 0 <= i < n -> aview segs (w_H W) mem' (res + i) = aview segs (w_H W) mem (p' + i)) ->
     val_mem segs (rdW W mem') (v + 16) 8 res ->
     val_mem segs (rdW W mem') (sp + 8) 8 (SHADOW_OFF + (v + 16) / 8) ->
     val_mem segs (rdW W mem') (sp + 16) 8 (fr + 32) -> val_mem segs (rdW W mem') (sp + 24) 8 n ->
     range_addressable (aview segs (w_H W) mem') SHADOW_OFF v 24 ->
     range_addressable (aview segs (w_H W) mem') SHADOW_OFF q 8 ->
     range_addressable (aview segs (w_H W) mem') SHADOW_OFF res (n + 1) ->
     res <> 0 ->
     SRr segs W (cfg_at segs (BASE + vrd_row 284) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 271) regs mem md) Q.
Proof.
intros P PLAW PCALL d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md sp fr p' n res Q
  HJ HPM R2 R9 R19 R20 R23 R27 R26 R10 Rgp Rtp Hsp Hal Hfr0 Hfr Hv0 Hv1 Hq0 Hq1 Hres Hn Hp'
  Dsv Dsq Dvq He0 Hlo Hhi Ho16 Hbud V16 V24 Vq HWN RAv Amv RAq Amq HCPY HNULL HNXT.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & HSTACK & _).
pose proof HSTACK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HES : ESTACK = 4096) by reflexivity.
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HP46 : 0 <= (2 : Z) ^ 46) by (apply Z.pow_nonneg; lia).
assert (HP47 : (2 : Z) ^ 46 <= 2 ^ 47) by (apply Z.pow_le_mono_r; lia).
assert (HP64 : (2 : Z) ^ 47 <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
assert (Hspc : alloc_ceiling <= sp - ESTACK) by lia.
(* the writable windows at row 271 *)
assert (Wst : forall o, 8 <= o < 16 -> writable_at segs (rdW W mem) (sp + o))
  by (intros o Ho; apply (apresent_writable segs); apply Hpres; lia).
assert (HFRP : forall a, wr_fp_frame (rd_fp q v) S0 ly a -> apresent (w_H W) mem a).
{ intros a (_ & cid & pos' & Hin & Hr).
  assert (Hin' : In (cid, pos') (frames S)) by (rewrite Hfrs; apply in_or_app; right; exact Hin).
  destruct (alx_frames segs B ARx LAWS ly S Hp W mem md cid pos' HAR Hin') as (_ & _ & Hb & _).
  unfold frame_rng, in_zr in Hr. cbn [fst snd] in Hr. exact (proj1 (Hb a Hr)). }
assert (Wnd : forall o, 16 <= o < 24 -> writable_at segs (rdW W mem) (v + o)).
{ intros o Ho. apply (apresent_writable segs). destruct (HWN (v + o) ltac:(lia)) as [Hw | Hw].
  - exact (proj1 (awr_byte_present_x (SK := SK) segs B prh_pst ARx LAWS
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hw)).
  - exact (HFRP _ Hw). }
assert (RAv16 : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (v + 16) 8)
  by (apply (vrd_ra_sub _ _ v 24); [exact RAv | lia | lia]).
assert (Amv16 : amem_range (v + 16) 8) by (apply (vrd_amem_sub v 24); [exact Amv | lia | lia | lia]).
destruct (vrd_st_271 W regs mem sp fr v q n p' R9 R26 R19 R20 R23 R27 Hsp Hal Hfr0 Hfr ltac:(lia) ltac:(lia)
  ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) Dvq V16 V24 Vq Wst Wnd RAv16 Amv16 RAq Amq)
  as [HS SHOK].
set (E := vrd_E2 regs n p') in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold vrd_E2; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs [w64 n; w64 p']) E)
  by (subst E; split; [intros nn Hnn; unfold vrd_E2; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EL : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm Hr; subst E; unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_nat regs _ m r Hr)).
assert (U9 : bv_unsigned (ew E 9) = sp)
  by (rewrite (EL 9%nat 9%bv) by (lia || reflexivity); rewrite R9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = v)
  by (rewrite (EL 19%nat 19%bv) by (lia || reflexivity); rewrite R19; apply unsigned_lit_small; lia).
assert (U10 : bv_unsigned (ew E 10) = res)
  by (rewrite (EL 10%nat 10%bv) by (lia || reflexivity); rewrite R10; apply unsigned_lit_small; lia).
assert (UO20 : U E (SOff 20 0) = q).
{ rewrite U_SOff. rewrite (EL 20%nat 20%bv) by (lia || reflexivity). rewrite R20, Z.add_0_r. unfold w64.
  rewrite unsigned_lit_small by lia. apply YP0m.zcanon_small. lia. }
assert (UO23 : U E (SOff 23 0) = SHADOW_OFF).
{ rewrite U_SOff. rewrite (EL 23%nat 23%bv) by (lia || reflexivity). rewrite R23, Z.add_0_r. unfold w64.
  rewrite unsigned_lit_small by lia. apply YP0m.zcanon_small. lia. }
assert (UO10 : U E (SOff 10 0) = res) by (rewrite U_SOff, U10, Z.add_0_r; apply YP0m.zcanon_small; lia).
assert (UO1916 : U E (SOff 19 16) = v + 16) by (rewrite U_SOff, U19; apply YP0m.zcanon_small; lia).
assert (Hqr : 0 <= q < 2 ^ 64) by lia.
pose (RUN := paj_run_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (RUNTO := paj_run_to_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (BR := paj_branch (PI := PI_prog_A)).
unfold cfg_at.
paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
{ (* the write premise *)
  intros a (r & Hin & Hr). vrd_rl Hin. repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U19 in Hr;
  first [ lia | left; unfold awr_byte; left; lia | apply HWN; lia ]. }
psrr_branch_tok RUN BR HS SHOK vrd_Bspan.
- (* row 277 taken: the NULL block *)
  rename Hc into H277.
  rewrite YI04.branch_eq_U, UO10, U_SLit, (YP0m.zcanon_small 0) in H277 by lia.
  apply Z.eqb_eq in H277.
  paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 326).
  { intros a (r & Hin & Hr). vrd_rl Hin. repeat (destruct Hin as [<- | Hin]); try contradiction;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U19 in Hr;
    first [ lia | left; unfold awr_byte; left; lia | apply HWN; lia ]. }
  pmkst HS.
  lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rq _ ?mq _) ?mdq) _ => apply (HNULL rq mq mdq HJ HPM) end.
  + vrd_tkr HS HAE UO20 UO23 R27 Hqr.
  + vrd_regv HS (Z_to_bv 5 25) (SOff 19 16) (v + 16) UO1916.
  + intros a Ha64 Hn1 Hn2. vrd_keep U9 U19 Ha64.
  + vrd_grow.
  + vrd_valg HS 19%nat 16.
    * cbn [base_val]. rewrite U19. reflexivity.
    * apply vrd_sv_eq. rewrite UO10. exact H277.
    * cbn; lia.
    * cbn; lia.
  + exact H277.
- (* row 277 not taken: rows 278..283 to the call of __asan_memcpy *)
  rename Hc into H277.
  rewrite YI04.branch_eq_U, UO10, U_SLit, (YP0m.zcanon_small 0) in H277 by slia.
  apply Z.eqb_neq in H277.
  destruct (HCPY H277) as (Hbc & Hblk & Amres & RAres & HLres & Dvr & Hpc & Dvp & Drp & Vsrc & Amp & RAp & HLp).
  paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
  { intros a (r & Hin & Hr). vrd_rl Hin. repeat (destruct Hin as [<- | Hin]); try contradiction;
    cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U19 in Hr;
    first [ slia | left; unfold awr_byte; left; slia | apply HWN; slia ]. }
  (* the state at the call *)
  lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ =>
    assert (KEEPT : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) -> ~ (sp + 8 <= a < sp + 16) ->
              aview segs (w_H W) (ms_mem msq) a = aview segs (w_H W) mem a)
      by (intros a Ha64 Hn1 Hn2; vrd_keep U9 U19 Ha64);
    assert (MGT : mem_grows (rdW W mem) (rdW W (ms_mem msq))) by vrd_grow
  end.
  rewrite ?wvb_collapse in HJ.
  lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ => set (msc := msq) in *; set (mdc := mdq) in * end.
  clearbody msc mdc.
  assert (E32 : ew E 32 = w64 n)
    by (subst E; unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; slia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = w64 p')
    by (subst E; unfold vrd_E2; rewrite Eimg_low by (unfold A_TEXT; slia); exact (ew_Ereg_extra regs _ 1)).
  assert (UO32 : U E (SOff 32 0) = n)
    by (rewrite U_SOff, E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by slia; apply YP0m.zcanon_small; slia).
  assert (UO33 : U E (SOff 33 0) = p')
    by (rewrite U_SOff, E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by slia; apply YP0m.zcanon_small; slia).
  assert (UO2 : U E (SOff 2 0) = sp).
  { rewrite U_SOff. rewrite (EL 2%nat 2%bv) by (slia || reflexivity). rewrite R2, Z.add_0_r. unfold w64.
    rewrite unsigned_lit_small by slia. apply YP0m.zcanon_small. slia. }
  assert (UO3 : U E (SOff 3 0) = bv_unsigned (getr regs 3)).
  { rewrite U_SOff. rewrite (EL 3%nat 3%bv) by (slia || reflexivity). rewrite Z.add_0_r.
    pose proof (u64_range (getr regs 3)) as Hr3. apply YP0m.zcanon_small. unfold M64 in *. slia. }
  assert (UO4 : U E (SOff 4 0) = bv_unsigned (getr regs 4)).
  { rewrite U_SOff. rewrite (EL 4%nat 4%bv) by (slia || reflexivity). rewrite Z.add_0_r.
    pose proof (u64_range (getr regs 4)) as Hr4. apply YP0m.zcanon_small. unfold M64 in *. slia. }
  assert (Q10 : getr (ms_regs msc) 10 = w64 res) by (vrd_regv HS (10%bv : bv 5) (SOff 10 0) res UO10).
  assert (Q11 : getr (ms_regs msc) 11 = w64 p') by (vrd_regv HS (11%bv : bv 5) (SOff 33 0) p' UO33).
  assert (Q12 : getr (ms_regs msc) 12 = w64 n) by (vrd_regv HS (12%bv : bv 5) (SOff 32 0) n UO32).
  assert (Q2 : getr (ms_regs msc) 2 = w64 sp) by (vrd_regv HS (2%bv : bv 5) (SOff 2 0) sp UO2).
  assert (Q3 : getr (ms_regs msc) 3 = w64 (bv_unsigned (getr regs 3)))
    by (vrd_regv HS (3%bv : bv 5) (SOff 3 0) (bv_unsigned (getr regs 3)) UO3).
  assert (Q4 : getr (ms_regs msc) 4 = w64 (bv_unsigned (getr regs 4)))
    by (vrd_regv HS (4%bv : bv 5) (SOff 4 0) (bv_unsigned (getr regs 4)) UO4).
  unfold w64 in Q3, Q4. rewrite Z_to_bv_bv_unsigned in Q3, Q4. rewrite Rgp in Q3. rewrite Rtp in Q4.
  assert (Q1 : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + vrd_row 284)).
  { first [ pose proof (st_ok_restrict_reg segs _ _ _ _ (1%bv : bv 5) HS) as QQ1
          | pose proof (st_ok_pi_restrict_reg _ _ _ _ (1%bv : bv 5) HS) as QQ1 ].
    lazymatch type of QQ1 with _ = sv_denot _ ?t =>
      replace t with (SOff A_TEXT (vrd_row 284)) in QQ1 by (vm_compute; reflexivity) end.
    rewrite (codeptr_val (PI := PI_prog_A) _ _ HEI) in QQ1. exact QQ1. }
  assert (HspT : spZ (ms_regs msc) = sp) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; slia).
  (* the memory at the call *)
  assert (KS : forall s, SHADOW_OFF <= s < kHighShadowEnd ->
            aview segs (w_H W) (ms_mem msc) s = aview segs (w_H W) mem s).
  { intros s Hs. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amv. apply KEEPT; slia. }
  assert (Hd8 : 0 <= (v + 16) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; slia).
  assert (VN : val_mem segs (rdW W (ms_mem msc)) (v + 16) 8 res).
  { vrd_valg HS 19%nat 16.
    - cbn [base_val]. rewrite U19. reflexivity.
    - apply vrd_sv_eq. exact UO10.
    - cbn. slia.
    - cbn. slia. }
  assert (VS8 : val_mem segs (rdW W (ms_mem msc)) (sp + 8) 8 (SHADOW_OFF + (v + 16) / 8)).
  { vrd_valg HS 9%nat 8.
    - cbn [base_val]. rewrite U9. reflexivity.
    - apply vrd_sv_eq. apply (vrd_U_shx _ 19 16); [exact UO1916 | exact UO23 | slia].
    - cbn. unfold SHADOW_OFF. slia.
    - cbn. slia. }
  assert (HSRC : 0 <= p' /\ p' + n <= 2 ^ 63 /\ src_ok segs W (ms_regs msc) (ms_mem msc) p' n /\
                 (res + n <= p' \/ p' + n <= res) /\ amem_range p' n /\
                 range_addressable (aview segs (w_H W) (ms_mem msc)) SHADOW_OFF p' n /\
                 (0 < n -> shadow_hull_vis (aview segs (w_H W) (ms_mem msc)) p' n)).
  { split; [slia|]. split; [slia|]. split.
    { intros a Ha. rewrite HspT. split; [|slia]. rewrite KEEPT by slia. exact (Vsrc a Ha). }
    split; [exact Drp|]. split; [exact Amp|]. split.
    - apply (vrd_ra_shkeep (w_H W) (w_H W) mem (ms_mem msc)); [slia | slia | exact KS | exact RAp].
    - intros Hn0. apply (vrd_hull_shkeep (w_H W) (w_H W) mem (ms_mem msc)); [slia | slia | slia | exact KS | exact (HLp Hn0)]. }
  pmkst HS.
  eapply SRr_bind.
  { exact (aj_intrin_at_xm (SK := SK) segs B prh_pst ARx LAWS (@pa_segs_low _ _ PI_prog_A) OCpy
      (pa_sigma AS___asan_memcpy) H_checked_memcpy_xm W (ms_regs msc) (ms_mem msc) (STK_parse_value d + e)
      (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp mdc k res p' n
      (sp - (spZ regs0 + e)) (Z_to_bv 64 (BASE + vrd_row 284)) HJ Q10 Q11 Q12 Hn ltac:(slia) ltac:(slia)
      ltac:(rewrite HspT; slia) Ho16 ltac:(slia) ltac:(slia) Q3 Q4 Q1
      ltac:(apply (ret_ok_codeptr_v (PI := PI_prog_A)); [unfold vrd_row; slia | reflexivity])
      ltac:(intros a Ha; split; [unfold awr_byte; right; right; left; apply Hblk; slia | slia])
      ltac:(apply (vrd_amem_sub res (n + 1)); [exact Amres | slia | slia | slia])
      ltac:(apply (vrd_ra_shkeep (w_H W) (w_H W) mem (ms_mem msc)); [slia | slia | exact KS |
              apply (vrd_ra_sub _ _ res (n + 1)); [exact RAres | slia | slia]])
      ltac:(intros Hn0; apply (vrd_hull_shkeep (w_H W) (w_H W) mem (ms_mem msc));
              [slia | slia | slia | exact KS | exact (HLres Hn0)])
      HSRC). }
  cbv beta. intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & R10b & HCP & HFR2 & HPR2 & HMN).
  pose proof (PCALL _ _ HMN HPM) as HPM2.
  cbv beta iota in HCP.
  replace (spZ regs0 + e + (sp - (spZ regs0 + e))) with sp in HFR2 by slia.
  assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) -> ~ (sp + 8 <= a < sp + 16) ->
            ~ (res <= a < res + n) -> ~ (sp - ESTACK <= a < sp) ->
            aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha H1 H2 H3 H4; rewrite (HFR2 a Ha H3 H4); exact (KEEPT a Ha H1 H2)).
  assert (KS2 : forall s, SHADOW_OFF <= s < kHighShadowEnd -> aview segs (w_H W) mem2 s = aview segs (w_H W) mem s).
  { intros s Hs. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amv, Amres. apply KEEP2; slia. }
  replace (mkCfg (mkst regs2 (Z_to_bv 64 (BASE + vrd_row 284)) mem2 (seg_rom segs)) md2)
    with (cfg_at segs (BASE + vrd_row 284) regs2 mem2 md2) by (unfold cfg_at, w64; reflexivity).
  apply (HNXT regs2 mem2 md2 HJ2 HPM2).
  + apply (vrd_tk_trans regs2 (ms_regs msc) regs); [apply vrd_tk_pres; exact HP2 |].
    vrd_tkr HS HAE UO20 UO23 R27 Hqr.
  + rewrite (HP2 25) by (unfold acallee_saved; slia). vrd_regv HS (Z_to_bv 5 25) (SOff 19 16) (v + 16) UO1916.
  + exact R10b.
  + exact KEEP2.
  + apply (vrd_mg_trans _ (rdW W (ms_mem msc))); [exact MGT | apply vrd_mg_of_pres; exact HPR2].
  + intros i Hi. rewrite (HCP i Hi). apply KEEPT; slia.
  + eapply val_mem_kept; [|exact VN]. intros kk Hk. apply HFR2; slia.
  + eapply val_mem_kept; [|exact VS8]. intros kk Hk. apply HFR2; slia.
  + eapply val_mem_kept; [|exact V16]. intros kk Hk. apply KEEP2; slia.
  + eapply val_mem_kept; [|exact V24]. intros kk Hk. apply KEEP2; slia.
  + apply (vrd_ra_shkeep (w_H W) (w_H W) mem mem2); [slia | slia | exact KS2 | exact RAv].
  + apply (vrd_ra_shkeep (w_H W) (w_H W) mem mem2); [slia | slia | exact KS2 | exact RAq].
  + apply (vrd_ra_shkeep (w_H W) (w_H W) mem mem2); [slia | slia | exact KS2 | exact RAres].
  + exact H277.
Qed.

(* the old statement, byte-identical: vrd_seg_271_P at P := fun _ => True *)
Lemma vrd_seg_271 : forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (sp fr p' n res : Z) (Q : world segs -> config -> Prop),
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  getr regs 2 = w64 sp -> getr regs 9 = w64 sp -> getr regs 19 = w64 v -> getr regs 20 = w64 q ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 27 = w64 (SHADOW_OFF + q / 8) -> getr regs 26 = w64 fr ->
  getr regs 10 = w64 res -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 -> 0 <= fr -> fr + 32 < 2 ^ 64 ->
  4096 <= v -> v + 24 <= 2 ^ 47 - 2 ^ 23 -> 4096 <= q -> q + 24 <= 2 ^ 47 ->
  0 <= res < 2 ^ 64 -> 0 <= n < 2 ^ 32 -> 0 <= p' < 2 ^ 64 ->
  (v + 24 <= sp - ESTACK \/ sp + 32 <= v + 16) -> (q + 8 <= sp - ESTACK \/ sp + 32 <= q) ->
  (v + 24 <= q \/ q + 8 <= v + 16) ->
  (* the frame facts of the caller's window (the instance discharges them, as for vrd_seg_267) *)
  0 <= e -> spZ regs0 - STK_parse_value d <= sp -> sp + 32 <= spZ regs0 + e ->
  (sp - (spZ regs0 + e)) mod 16 = 0 -> ESTACK + (spZ regs0 + e - sp) <= STK_parse_value d + e ->
  val_mem segs (rdW W mem) (sp + 16) 8 (fr + 32) -> val_mem segs (rdW W mem) (sp + 24) 8 n ->
  val_mem segs (rdW W mem) q 8 p' ->
  (* the node's str word may be written (prhPv_node's home: a block, a caller's live fake frame, the window) *)
  (forall a, v + 16 <= a < v + 24 ->
     awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly S) ly
       [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly a) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 24 -> amem_range v 24 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 8 -> amem_range q 8 ->
  (* the memcpy's premises, when the block is not NULL (prh_alloc_post's success arm; the token in the text) *)
  (res <> 0 ->
     res + n + 1 <= alloc_ceiling /\
     (forall a, res <= a < res + n + 1 -> in_tmp_block (ablocks B ly0 S0) (ablocks B ly S) a) /\
     amem_range res (n + 1) /\ range_addressable (aview segs (w_H W) mem) SHADOW_OFF res (n + 1) /\
     (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) res n) /\
     (v + 24 <= res \/ res + n + 1 <= v + 16) /\
     p' + n <= alloc_ceiling /\ (p' + n <= v + 16 \/ v + 24 <= p') /\ (res + n <= p' \/ p' + n <= res) /\
     (forall a, p' <= a < p' + n -> aview segs (w_H W) mem a <> None) /\ amem_range p' n /\
     range_addressable (aview segs (w_H W) mem) SHADOW_OFF p' n /\
     (0 < n -> shadow_hull_vis (aview segs (w_H W) mem) p' n)) ->
  (* row 326: the NULL block, stored in the node *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k ->
     vrd_tk regs' regs -> getr regs' (Z_to_bv 5 25) = w64 (v + 16) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) -> ~ (sp + 8 <= a < sp + 16) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     val_mem segs (rdW W mem') (v + 16) 8 0 -> res = 0 ->
     SRr segs W (cfg_at segs (BASE + vrd_row 326) regs' mem' md') Q) ->
  (* row 284: the block in the node, the token copied into it *)
  (forall (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model),
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k ->
     vrd_tk regs' regs -> getr regs' (Z_to_bv 5 25) = w64 (v + 16) -> getr regs' 10 = w64 res ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (v + 16 <= a < v + 24) -> ~ (sp + 8 <= a < sp + 16) ->
        ~ (res <= a < res + n) -> ~ (sp - ESTACK <= a < sp) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     (forall i, 0 <= i < n -> aview segs (w_H W) mem' (res + i) = aview segs (w_H W) mem (p' + i)) ->
     val_mem segs (rdW W mem') (v + 16) 8 res ->
     val_mem segs (rdW W mem') (sp + 8) 8 (SHADOW_OFF + (v + 16) / 8) ->
     val_mem segs (rdW W mem') (sp + 16) 8 (fr + 32) -> val_mem segs (rdW W mem') (sp + 24) 8 n ->
     range_addressable (aview segs (w_H W) mem') SHADOW_OFF v 24 ->
     range_addressable (aview segs (w_H W) mem') SHADOW_OFF q 8 ->
     range_addressable (aview segs (w_H W) mem') SHADOW_OFF res (n + 1) ->
     res <> 0 ->
     SRr segs W (cfg_at segs (BASE + vrd_row 284) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 271) regs mem md) Q.
Proof.
intros d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md sp fr p' n res Q
  HJ R2 R9 R19 R20 R23 R27 R26 R10 Rgp Rtp Hsp Hal Hfr0 Hfr Hv0 Hv1 Hq0 Hq1 Hres Hn Hp'
  Dsv Dsq Dvq He0 Hlo Hhi Ho16 Hbud V16 V24 Vq HWN RAv Amv RAq Amq HCPY HNULL HNXT.
exact (vrd_seg_271_P (fun _ => True) (srr_inv_laws_true segs) vrd_true_call d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos
  ly S Hp k W regs mem md sp fr p' n res Q
  HJ I R2 R9 R19 R20 R23 R27 R26 R10 Rgp Rtp Hsp Hal Hfr0 Hfr Hv0 Hv1 Hq0 Hq1 Hres Hn Hp'
  Dsv Dsq Dvq He0 Hlo Hhi Ho16 Hbud V16 V24 Vq HWN RAv Amv RAq Amq HCPY
  (fun regs' mem' md' HJ' _ => HNULL regs' mem' md' HJ')
  (fun regs' mem' md' HJ' _ => HNXT regs' mem' md' HJ')).
Qed.

(* ======================================================================================================== *)
(* ROWS 284..298: the shadow of v + 16 again, the NUL at res + n, the strtod call                              *)
(* ======================================================================================================== *)

(* pin a register to another symbolic value with the same denotation *)
Lemma vrd_pin : forall E ss ms (r : bv 5) e',
  st_ok_pi segs VAL E ss ms -> sv_denot E e' = getr (ms_regs ms) r -> bv_eqb r 0 = false ->
  st_ok_pi segs VAL E (mkSS (ss_pc ss) (sr_set (ss_regs ss) r e') (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms.
Proof.
intros E ss ms r e' HS Hr Hr0. unfold st_ok_pi, abs_ss, setpc in *. cbn [ss_pc ss_regs ss_fregs ss_mem ss_resv ss_facts] in *.
apply (st_ok_regs segs E (mkSST (BASE + ss_pc ss) (ss_regs ss) (ss_fregs ss) (ss_mem ss) (ss_resv ss) (ss_facts ss)) ms
  (sr_set (ss_regs ss) r e') HS).
intros rr. cbn [ss_regs]. destruct (decide (rr = r)) as [->|Hne].
- rewrite sr_get_set_same by exact Hr0. pose proof (st_ok_reg segs E _ ms r HS) as Hq. cbn [ss_regs] in Hq.
  rewrite <- Hq. exact Hr.
- rewrite sr_get_set_other by exact Hne. reflexivity.
Qed.

(* an atom below a token atom keeps its value in the run's extended environment *)
Lemma vrd_U_ewset : forall E k x m o, m <> k -> U (ewset E k x) (SOff m o) = U E (SOff m o).
Proof. intros E k x m o Hm. rewrite !U_SOff, ew_ewset_other by exact Hm. reflexivity. Qed.

(* a byte array kept byte by byte, and the NUL appended *)
Lemma vrd_garr8_keep : forall (H : word -> bool) (m m' : word -> option byte) base l,
  (forall j, (j < length l)%nat -> aview segs H m' (base + Z.of_nat j) = aview segs H m (base + Z.of_nat j)) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H m') base l.
Proof.
intros H m m' base l HK HG j Hj. destruct (HG j Hj) as [HV HR]. split; [|exact HR].
eapply val_mem_kept; [|exact HV]. intros kk Hk. cbn in Hk. replace kk with 0 by lia. rewrite Z.add_0_r.
apply HK. exact Hj.
Qed.
Lemma vrd_garr8_snoc : forall (m : word -> option byte) base l,
  garr8 segs m base l -> val_mem segs m (base + Z.of_nat (length l)) 1 0 -> garr8 segs m base (l ++ [0]).
Proof.
intros m base l HG HV j Hj. rewrite length_app in Hj. cbn [length] in Hj.
destruct (Nat.lt_ge_cases j (length l)) as [Hlt|Hge].
- rewrite app_nth1 by exact Hlt. exact (HG j Hlt).
- assert (Hj' : j = length l) by lia. subst j. rewrite app_nth2 by lia. rewrite Nat.sub_diag. cbn [nth].
  split; [exact HV | lia].
Qed.

Local Ltac vrd_inw3 Ua Ub Uc :=
  let r := fresh "r" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin & Hr); vrd_rl Hin; repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Ua, ?Ub, ?Uc in Hr; lia.
Local Ltac vrd_keep3 Ua Ub Uc Ha64 :=
  repeat match goal with
  | HFx : frame_of _ ?rs (mrestrict ?Hh ?m1) (mrestrict ?Hh ?m2) |- aview _ ?Hh ?m2 ?a = _ =>
      transitivity (aview segs Hh m1 a);
      [ apply (vrd_fr_aview _ rs Hh m1 m2 a HFx Ha64); vrd_inw3 Ua Ub Uc | clear HFx ]
  end; reflexivity.
(* vrd_tk after a run whose state holds every kept register as its own atom (s11 included) *)
Local Ltac vrd_tkr_a HS HAE :=
  let r := fresh "r" in let Hr := fresh "Hr" in let H25 := fresh "H25" in let Hin := fresh "Hin" in
  intros r Hr H25; destruct (vrd_cs_split r Hr H25) as [-> | Hin];
  [ first [ exact (regs_kept_of_st_ok_pi _ _ _ _ _ [Z_to_bv 5 27] HS HAE ltac:(vm_compute; reflexivity) _ (or_introl eq_refl))
          | exact (regs_kept_of_st_ok segs _ _ _ _ _ [Z_to_bv 5 27] HS HAE ltac:(vm_compute; reflexivity) _ (or_introl eq_refl)) ]
  | first [ exact (regs_kept_of_st_ok_pi _ _ _ _ _ vrd_tk_l HS HAE ltac:(vm_compute; reflexivity) _ Hin)
          | exact (regs_kept_of_st_ok segs _ _ _ _ _ vrd_tk_l HS HAE ltac:(vm_compute; reflexivity) _ Hin) ] ].

(* ---- the state at row 284 (A 0x86378), after the memcpy: the stack slots (the shadow address of v + 16 at sp + 8,
   fr + 32 at sp + 16, n at sp + 24; nothing written), the node's str word holding the block res, and the block's
   last byte res + n (writable: the NUL of row 294). s9 = v + 16 (row 271). Extra atoms: 32 = n, 33 = res,
   34 = res + n; a0 is pinned to atom 34 at row 290 (rows 287..289 compute it as n + res), so the store of row 294
   finds its region. Measured by symbolic execution: run to row 290; pinned, the run reaches the strtod call
   with two shadow tokens (the partial granule of res + n, rows 290..293 and the slow path at rows 341..342) and
   sh_obls = []. ---- *)
Definition vrd_E3 (regs : bvmap 5 word) (x y z : Z) : env :=
  @Eimg _ A_prog_listing PI_prog_A (Ereg regs [w64 x; w64 y; w64 z]).
Definition vrd_284_sr : list sv := sr_set sr_atoms 25%bv (SOff 19 16).
Definition vrd_284_regions : smem :=
  [ YP09.mkRegion (Some 9%nat) 0 32 0 0
      [YP09.mkChunk 8 (CVal 8 (vrd_shx 19 16)); YP09.mkChunk 16 (CVal 8 (SOff 26 32));
       YP09.mkChunk 24 (CVal 8 (SOff 32 0))];
    YP09.mkRegion (Some 19%nat) 16 24 0 0 [YP09.mkChunk 16 (CVal 8 (SOff 33 0))];
    YP09.mkRegion (Some 34%nat) 0 1 0 1 [] ].
Definition vrd_284_facts : facts := mkFacts
  [ (9%nat, mkAF (2 ^ 46) (2 ^ 47 - 32) 5); (19%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0);
    (23%nat, mkAF SHADOW_OFF SHADOW_OFF 0); (32%nat, mkAF 0 (2 ^ 32 - 1) 0);
    (33%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0); (34%nat, mkAF 4096 (2 ^ 47 - 2 ^ 23) 0) ] [] [].
Definition ss_vrd_284 : sstate := mkSS (vrd_row 284) vrd_284_sr vrd_284_regions None vrd_284_facts.
Definition vrd_SH284 : list shent := [mkSHE 19 16 24; mkSHE 34 0 1].

Lemma vrd_st_284 : forall (W : world segs) regs mem (sp fr v n res : Z),
  getr regs 9 = w64 sp -> getr regs 26 = w64 fr -> getr regs 19 = w64 v -> getr regs (Z_to_bv 5 25) = w64 (v + 16) ->
  getr regs 23 = w64 SHADOW_OFF ->
  2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 -> 0 <= fr -> fr + 32 < 2 ^ 64 ->
  4096 <= v -> v + 24 <= 2 ^ 47 - 2 ^ 23 -> 0 <= n < 2 ^ 32 -> 4096 <= res -> res + n + 1 <= 2 ^ 47 - 2 ^ 23 ->
  (v + 24 <= sp \/ sp + 32 <= v + 16) -> (res + n + 1 <= sp \/ sp + 32 <= res + n) ->
  (v + 24 <= res + n \/ res + n + 1 <= v + 16) ->
  val_mem segs (rdW W mem) (sp + 8) 8 (SHADOW_OFF + (v + 16) / 8) ->
  val_mem segs (rdW W mem) (sp + 16) 8 (fr + 32) -> val_mem segs (rdW W mem) (sp + 24) 8 n ->
  val_mem segs (rdW W mem) (v + 16) 8 res -> writable_at segs (rdW W mem) (res + n) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (v + 16) 8 -> amem_range (v + 16) 8 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (res + n) 1 -> amem_range (res + n) 1 ->
  st_ok_pi segs VAL (vrd_E3 regs n res (res + n)) ss_vrd_284
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + vrd_row 284)) mem (seg_rom segs))) /\
  sh_ok segs vrd_Bx vrd_SH284 (vrd_E3 regs n res (res + n)) (rdW W mem).
Proof.
intros W regs mem sp fr v n res R9 R26 R19 R25 R23 Hsp Hal Hfr0 Hfr Hv0 Hv1 Hn Hr0 Hr1 Dsv Dsr Dvr
  V8 V16 V24 Vv Wnul RAv Amv RAn Amn.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
set (E := vrd_E3 regs n res (res + n)).
assert (EL : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm Hr; subst E; unfold vrd_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ m r Hr)).
assert (E32 : ew E 32 = w64 n)
  by (subst E; unfold vrd_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 res)
  by (subst E; unfold vrd_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (res + n))
  by (subst E; unfold vrd_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew E 9) = sp)
  by (rewrite (EL 9%nat 9%bv) by (lia || reflexivity); rewrite R9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = v)
  by (rewrite (EL 19%nat 19%bv) by (lia || reflexivity); rewrite R19; apply unsigned_lit_small; lia).
assert (U23 : bv_unsigned (ew E 23) = SHADOW_OFF)
  by (rewrite (EL 23%nat 23%bv) by (lia || reflexivity); rewrite R23; apply unsigned_lit_small;
      unfold SHADOW_OFF; lia).
assert (U26 : bv_unsigned (ew E 26) = fr)
  by (rewrite (EL 26%nat 26%bv) by (lia || reflexivity); rewrite R26; apply unsigned_lit_small; lia).
assert (U32 : bv_unsigned (ew E 32) = n) by (rewrite E32; apply unsigned_lit_small; lia).
assert (U33 : bv_unsigned (ew E 33) = res) by (rewrite E33; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = res + n) by (rewrite E34; apply unsigned_lit_small; lia).
assert (UO1916 : U E (SOff 19 16) = v + 16) by (rewrite U_SOff, U19; apply YP0m.zcanon_small; lia).
assert (UO23 : U E (SOff 23 0) = SHADOW_OFF)
  by (rewrite U_SOff, U23, Z.add_0_r; apply YP0m.zcanon_small; unfold SHADOW_OFF; lia).
assert (Hd8 : 0 <= (v + 16) / 8 < 2 ^ 61) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
split.
- rewrite restrict_mkst_fx. apply pa_entry_st_ok_full.
  + unfold vrd_284_sr. apply regs_ok_pin; [apply regs_ok_Eimg_Ereg | discriminate |].
    replace (25%bv : bv 5) with (Z_to_bv 5 25) by (apply bv_eq; reflexivity). rewrite R25.
    symmetry. apply vrd_sv_eq. exact UO1916.
  + vm_compute. reflexivity.
  + unfold vrd_284_regions. repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
    cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
    * rewrite U9. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat constructor.
      -- apply (chunk_ok_val segs _ _ sp 8 8 (vrd_shx 19 16) (SHADOW_OFF + (v + 16) / 8));
           [apply vrd_sv_eq; apply (vrd_U_shx _ 19 16); [exact UO1916 | exact UO23 | lia] | cbn; lia | lia | exact V8].
      -- apply (chunk_ok_val segs _ _ sp 16 8 (SOff 26 32) (fr + 32));
           [apply vrd_sv_eq; rewrite U_SOff, U26; apply YP0m.zcanon_small; lia | cbn; lia | lia | exact V16].
      -- apply (chunk_ok_val segs _ _ sp 24 8 (SOff 32 0) n);
           [apply vrd_sv_eq; rewrite U_SOff, U32, Z.add_0_r; apply YP0m.zcanon_small; lia | cbn; lia | lia | exact V24].
    * rewrite U19. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
      repeat constructor.
      apply (chunk_ok_val segs _ _ v 16 8 (SOff 33 0) res);
        [apply vrd_sv_eq; rewrite U_SOff, U33, Z.add_0_r; apply YP0m.zcanon_small; lia | cbn; lia | lia | exact Vv].
    * rewrite U34. split; [lia|]. split; [lia|].
      split; [intros o Ho; replace o with 0 by lia; rewrite Z.add_0_r; exact Wnul | constructor].
  + apply pairwise_disjoint_of_extents. unfold vrd_284_regions, extent_of_region.
    cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val zpairwise_disjoint zall_disjoint].
    rewrite U9, U19, U34. unfold zdisj. cbn [fst snd]. repeat split; first [lia | left; lia | right; lia].
  + split; [|split; [exact I | exact I]].
    cbn [vrd_284_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
    rewrite U9, U19, U23, U32, U33, U34. change (2 ^ 0) with 1. change (2 ^ 5) with 32. rewrite !Z.mod_1_r.
    repeat split; try lia; try exact I.
- unfold sh_ok, vrd_SH284. repeat (apply Forall_cons); try apply Forall_nil.
  + apply (shent_ok_of_range segs (w_H W) mem _ vrd_Bx 19 (v + 16) 8 v 16 24 RAv).
    * unfold vrd_Bx. exact UO23.
    * rewrite YP0e.U_SOff, U19, Z.add_0_r. apply YP0m.zcanon_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amv. lia.
  + apply (shent_ok_of_range segs (w_H W) mem _ vrd_Bx 34 (res + n) 1 (res + n) 0 1 RAn).
    * unfold vrd_Bx. exact UO23.
    * rewrite YP0e.U_SOff, U34, Z.add_0_r. apply YP0m.zcanon_small. lia.
    * lia.
    * lia.
    * intros x Hx. cbn [Z.min Z.max] in Hx. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amn. lia.
Qed.

(* the three image facts about B the strtod row needs (VrdNum.v's, an instance proves them of its own B) *)
Hypothesis B_tp : as_tp B = STRTOD_TP.
Hypothesis B_errno : as_errno B = STRTOD_ERRNO.
Hypothesis B_errno_own : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).

(* ---- SEGMENT 284, rows 284..298 (A 0x86378..0x863b0) and the strtod call. Rows 284..286: the shadow of v + 16
   through the spilled address (0); rows 287..289: a0 = v->str + n = res + n; rows 290..293: its shadow, a partial
   granule (the slow path at rows 341..342 passes, n + 1 bytes are addressable); row 294: the NUL; rows 295..298:
   a0 = v->str = res, s9 = a1 = fr + 32 (from sp + 16) and `jal strtod` (VrdNum.vrd_strtod_row at
   YStrtodRowX.aj_strtod_row). The continuation runs at row 299 at strtod's float state fx'.
   THE MEMORY INVARIANT P across the call: the row takes memnorm of the memory at the call (strtod_site_x's last
   conjunct), which srr_inv_mn gives from P there, and its post ends with memnorm of the memory after the call, which
   srr_inv_call turns into P there. So memnorm is read at THIS memory only, never claimed of every allocator state:
   the earlier Section hypothesis that claimed memnorm at every ARx state (unprovable; A2Top's finding, a Theorem Labs lane's
   12:19Z measurement) is DELETED, and with it the old statement vrd_seg_284, whose proof needed it (nothing outside
   this file cited it). ---- *)
Lemma vrd_seg_284_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P -> srr_inv_call segs P ->
  srr_inv_mn segs P ->
  forall d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k
    (W : world segs) regs mem md (sp fr n res : Z) (txt : list Z) (Q : world segs -> config -> Prop),
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp W mem md k ->
  P mem ->
  getr regs 2 = w64 sp -> getr regs 9 = w64 sp -> getr regs 19 = w64 v -> getr regs (Z_to_bv 5 25) = w64 (v + 16) ->
  getr regs 23 = w64 SHADOW_OFF -> getr regs 26 = w64 fr -> getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
  2 ^ 46 <= sp <= 2 ^ 47 - 32 -> sp mod 32 = 0 -> 0 <= fr -> 4096 <= v -> v + 24 <= 2 ^ 47 - 2 ^ 23 ->
  0 <= q -> q + 8 <= 2 ^ 47 ->
  Z.of_nat (length txt) = n -> 0 <= n < 2 ^ 32 -> 4096 <= res -> res + n + 1 <= alloc_ceiling ->
  (v + 24 <= sp \/ sp + 32 <= v + 16) -> (v + 24 <= res + n \/ res + n + 1 <= v + 16) ->
  0 <= e -> spZ regs0 - STK_parse_value d <= sp -> sp + 32 <= spZ regs0 + e ->
  (sp - (spZ regs0 + e)) mod 16 = 0 -> STK_RT_STRTOD + (spZ regs0 + e - sp) <= STK_parse_value d + e ->
  val_mem segs (rdW W mem) (sp + 8) 8 (SHADOW_OFF + (v + 16) / 8) ->
  val_mem segs (rdW W mem) (sp + 16) 8 (fr + 32) -> val_mem segs (rdW W mem) (sp + 24) 8 n ->
  val_mem segs (rdW W mem) (v + 16) 8 res -> garr8 segs (rdW W mem) res txt ->
  (forall a, res <= a < res + n + 1 -> in_tmp_block (ablocks B ly0 S0) (ablocks B ly S) a) ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 24 -> amem_range v 24 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 8 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF res (n + 1) -> amem_range res (n + 1) ->
  (* the strtod row's premises: the token, the endptr cell fr + 32 in this call's own fake frame, the GOT guard *)
  vrd_txt_ok txt -> frm_zero (@YK11.fp_csr fx) ->
  (forall a, fr + 32 <= a < fr + 32 + 8 ->
     awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly S) ly
       [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly a) ->
  fr + 40 <= sp - STK_RT_STRTOD -> amem_range (fr + 32) 8 -> (fr + 40 <= res \/ res + n + 1 <= fr + 32) ->
  (res + n + 1 <= si_img_lo strtod_img_A \/ si_globals_top strtod_img_A <= res) ->
  si_globals_top strtod_img_A <= fr + 32 ->
  (forall a, si_got_guard strtod_img_A <= a < si_got_guard strtod_img_A + 8 ->
     aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))) ->
  (* row 299, at strtod's float state *)
  (forall (fx' : YK11.FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) (md' : Model) (bits c : Z),
     frm_zero (@YK11.fp_csr fx') -> fregs_kept_x fx fx' ->
     LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fx') (Z_to_bv 5 10) = Z_to_bv 64 bits ->
     vrd_sm txt = Some (bits, c) -> 0 <= c <= n ->
     AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
        ly S Hp W mem' md' k -> P mem' ->
     vrd_tk regs' regs -> getr regs' (Z_to_bv 5 25) = w64 (fr + 32) ->
     (forall a, 0 <= a < 2 ^ 64 -> ~ (res + n <= a < res + n + 1) -> ~ (fr + 32 <= a < fr + 40) ->
        ~ (sp - STK_RT_STRTOD <= a < sp) -> ~ (as_errno B <= a < as_errno B + 4) ->
        aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
     mem_grows (rdW W mem) (rdW W mem') ->
     val_mem segs (rdW W mem') (fr + 32) 8 (res + c) ->
     garr8 segs (rdW W mem') res (txt ++ [0]) ->
     range_addressable (aview segs (w_H W) mem') SHADOW_OFF v 24 ->
     range_addressable (aview segs (w_H W) mem') SHADOW_OFF q 8 ->
     range_addressable (aview segs (w_H W) mem') SHADOW_OFF res (n + 1) ->
     SRr segs W (cfg_at (fx := fx') segs (BASE + vrd_row 299) regs' mem' md') Q) ->
  SRr segs W (cfg_at segs (BASE + vrd_row 284) regs mem md) Q.
Proof.
intros P PLAW PCALL PMN d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs mem md sp fr n res txt Q
  HJ HPM R2 R9 R19 R25 R23 R26 Rgp Rtp Hsp Hal Hfr0 Hv0 Hv1 Hq0 Hq1 Hlen Hn Hr0 Hr1 Dsv Dvr He0 Hlo Hhi Ho16 Hbud
  V8 V16 V24 Vv GT Hblk RAv Amv RAq RAres Amres TXT FRM HEW HES Ame Der Hgr Hge GOT HNXT.
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & _ & _ & _ & _ & _ & Hpres & HSTACK & _).
pose proof HSTACK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & Eslo & Eshi & _).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HKS : STK_RT_STRTOD = 16384) by reflexivity.
assert (HGT : si_globals_top strtod_img_A = 6291456) by reflexivity.
assert (HIL : si_img_lo strtod_img_A = 65536) by reflexivity.
assert (HGG : si_got_guard strtod_img_A = 666776) by reflexivity.
assert (HER : as_errno B = 6151756) by (rewrite B_errno; reflexivity).
assert (HP46 : 0 <= (2 : Z) ^ 46) by (apply Z.pow_nonneg; lia).
assert (HP47 : (2 : Z) ^ 46 <= 2 ^ 47) by (apply Z.pow_le_mono_r; lia).
assert (HP64 : (2 : Z) ^ 47 <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
assert (Hspc : alloc_ceiling <= sp - STK_RT_STRTOD) by lia.
(* the NUL's byte is writable: a byte of the new block *)
assert (Wnul : writable_at segs (rdW W mem) (res + n)).
{ apply (apresent_writable segs).
  assert (Hw : awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly S) ly
                 [(0, pos)] (res + n)) by (unfold awr_byte; right; right; left; apply Hblk; lia).
  exact (proj1 (awr_byte_present_x (SK := SK) segs B prh_pst ARx LAWS
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ Hw)). }
assert (RAv16 : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (v + 16) 8)
  by (apply (vrd_ra_sub _ _ v 24); [exact RAv | lia | lia]).
assert (Amv16 : amem_range (v + 16) 8) by (apply (vrd_amem_sub v 24); [exact Amv | lia | lia | lia]).
assert (RAn : range_addressable (aview segs (w_H W) mem) SHADOW_OFF (res + n) 1)
  by (apply (vrd_ra_sub _ _ res (n + 1)); [exact RAres | lia | lia]).
assert (Amn : amem_range (res + n) 1) by (apply (vrd_amem_sub res (n + 1)); [exact Amres | lia | lia | lia]).
destruct (vrd_st_284 W regs mem sp fr v n res R9 R26 R19 R25 R23 Hsp Hal Hfr0 ltac:(lia) Hv0 Hv1 Hn Hr0
  ltac:(lia) Dsv ltac:(lia) Dvr V8 V16 V24 Vv Wnul RAv16 Amv16 RAn Amn) as [HS SHOK].
set (E := vrd_E3 regs n res (res + n)) in *.
assert (HEI : img_env VAL A_LIM E) by (subst E; unfold vrd_E3; apply Eimg_env).
assert (EL : forall m (r : bv 5), (m < 32)%nat -> Z.of_nat m = bv_unsigned r -> ew E m = getr regs r)
  by (intros m r Hm Hr; subst E; unfold vrd_E3; rewrite Eimg_low by (unfold A_TEXT; lia);
      exact (ew_Ereg_nat regs _ m r Hr)).
assert (E32 : ew E 32 = w64 n)
  by (subst E; unfold vrd_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = w64 res)
  by (subst E; unfold vrd_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = w64 (res + n))
  by (subst E; unfold vrd_E3; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (U9 : bv_unsigned (ew E 9) = sp)
  by (rewrite (EL 9%nat 9%bv) by (lia || reflexivity); rewrite R9; apply unsigned_lit_small; lia).
assert (U19 : bv_unsigned (ew E 19) = v)
  by (rewrite (EL 19%nat 19%bv) by (lia || reflexivity); rewrite R19; apply unsigned_lit_small; lia).
assert (U34 : bv_unsigned (ew E 34) = res + n) by (rewrite E34; apply unsigned_lit_small; lia).
assert (UO32 : U E (SOff 32 0) = n)
  by (rewrite U_SOff, E32, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; apply YP0m.zcanon_small; lia).
assert (UO33 : U E (SOff 33 0) = res)
  by (rewrite U_SOff, E33, Z.add_0_r; unfold w64; rewrite unsigned_lit_small by lia; apply YP0m.zcanon_small; lia).
assert (UO34 : U E (SOff 34 0) = res + n) by (rewrite U_SOff, U34, Z.add_0_r; apply YP0m.zcanon_small; lia).
assert (UO2632 : U E (SOff 26 32) = fr + 32).
{ rewrite U_SOff. rewrite (EL 26%nat 26%bv) by (lia || reflexivity). rewrite R26. unfold w64.
  rewrite unsigned_lit_small by lia. apply YP0m.zcanon_small. lia. }
assert (UO2 : U E (SOff 2 0) = sp).
{ rewrite U_SOff. rewrite (EL 2%nat 2%bv) by (lia || reflexivity). rewrite R2, Z.add_0_r. unfold w64.
  rewrite unsigned_lit_small by lia. apply YP0m.zcanon_small. lia. }
assert (UO3 : U E (SOff 3 0) = bv_unsigned (getr regs 3)).
{ rewrite U_SOff. rewrite (EL 3%nat 3%bv) by (lia || reflexivity). rewrite Z.add_0_r.
  pose proof (u64_range (getr regs 3)) as Hr3. apply YP0m.zcanon_small. unfold M64 in *. lia. }
assert (UO4 : U E (SOff 4 0) = bv_unsigned (getr regs 4)).
{ rewrite U_SOff. rewrite (EL 4%nat 4%bv) by (lia || reflexivity). rewrite Z.add_0_r.
  pose proof (u64_range (getr regs 4)) as Hr4. apply YP0m.zcanon_small. unfold M64 in *. lia. }
pose (RUN := paj_run_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
pose (RUNTO := paj_run_to_xf_inv (SK := SK) (PL := PL_prog_A) (PI := PI_prog_A) B prh_pst ARx LAWS P PLAW).
unfold cfg_at.
paj_run_to_tok_x_inv RUNTO HS HJ SHOK HPM vrd_Bspan (vrd_row 290).
{ intros a (r & Hin & Hr). vrd_rl Hin. repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U19, ?U34 in Hr;
  first [ lia | left; unfold awr_byte; right; right; left; apply Hblk; lia ]. }
(* row 290: a0 = n + res, pinned to atom 34 *)
pose proof (st_ok_pi_restrict_reg _ _ _ _ (10%bv : bv 5) HS) as Q10a.
lazymatch type of Q10a with _ = sv_denot _ ?t =>
  replace t with (SAlu ALU_ADD (SOff 32 0) (SOff 33 0)) in Q10a by (vm_compute; reflexivity) end.
assert (UA : U E (SAlu ALU_ADD (SOff 32 0) (SOff 33 0)) = res + n).
{ rewrite U_SAlu, UO32, UO33. cbn [zalu_raw]. replace (n + res) with (res + n) by lia.
  apply YP0m.zcanon_small. lia. }
rewrite (vrd_sv_eq _ _ _ UA) in Q10a.
lazymatch type of Q10a with getr (ms_regs ?msq) _ = _ =>
  assert (HPIN : sv_denot E (SOff 34 0) = getr (ms_regs msq) 10)
    by (rewrite Q10a; exact (vrd_sv_eq _ _ _ UO34));
  pose proof (vrd_pin _ _ _ (10%bv : bv 5) (SOff 34 0) HS HPIN eq_refl) as HS2
end.
clear HS Q10a. rename HS2 into HS.
paj_run_tok_x_inv RUN HS HJ SHOK HPM vrd_Bspan.
{ intros a (r & Hin & Hr). vrd_rl Hin. repeat (destruct Hin as [<- | Hin]); try contradiction;
  cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9, ?U19, ?U34 in Hr;
  first [ lia | left; unfold awr_byte; right; right; left; apply Hblk; lia ]. }
(* the state at the strtod call *)
lazymatch goal with |- SRr _ _ (mkCfg ?msq _) _ =>
  assert (KEEPT : forall a, 0 <= a < 2 ^ 64 -> ~ (res + n <= a < res + n + 1) ->
            aview segs (w_H W) (ms_mem msq) a = aview segs (w_H W) mem a)
    by (intros a Ha64 Hn1; vrd_keep3 U9 U19 U34 Ha64);
  assert (MGT : mem_grows (rdW W mem) (rdW W (ms_mem msq))) by vrd_grow
end.
rewrite ?wvb_collapse in HJ.
lazymatch goal with |- SRr _ _ (mkCfg ?msq ?mdq) _ => set (msc := msq) in *; set (mdc := mdq) in * end.
clearbody msc mdc.
lazymatch type of HS with st_ok _ ?E' _ _ => set (E2 := E') in * end.
assert (HEI2 : img_env VAL A_LIM E2) by (lazymatch goal with H : img_env _ _ E2 |- _ => exact H end).
assert (HAE2 : env_agree 32 (Ereg regs [w64 n; w64 res; w64 (res + n)]) E2).
{ unfold E2. split; [|reflexivity]. intros nn Hnn. rewrite !ew_ewset_other by lia.
  subst E. unfold vrd_E3. apply Eimg_low. unfold A_TEXT. lia. }
assert (UO33' : U E2 (SOff 33 0) = res) by (unfold E2; rewrite !vrd_U_ewset by lia; exact UO33).
assert (UO2632' : U E2 (SOff 26 32) = fr + 32) by (unfold E2; rewrite !vrd_U_ewset by lia; exact UO2632).
assert (UO2' : U E2 (SOff 2 0) = sp) by (unfold E2; rewrite !vrd_U_ewset by lia; exact UO2).
assert (UO3' : U E2 (SOff 3 0) = bv_unsigned (getr regs 3)) by (unfold E2; rewrite !vrd_U_ewset by lia; exact UO3).
assert (UO4' : U E2 (SOff 4 0) = bv_unsigned (getr regs 4)) by (unfold E2; rewrite !vrd_U_ewset by lia; exact UO4).
assert (U34' : bv_unsigned (ew E2 34) = res + n) by (unfold E2; rewrite !ew_ewset_other by lia; exact U34).
assert (Q10 : getr (ms_regs msc) 10 = w64 res) by (vrd_regv HS (10%bv : bv 5) (SOff 33 0) res UO33').
assert (Q11 : getr (ms_regs msc) 11 = w64 (fr + 32)) by (vrd_regv HS (11%bv : bv 5) (SOff 26 32) (fr + 32) UO2632').
assert (Q2 : getr (ms_regs msc) 2 = w64 sp) by (vrd_regv HS (2%bv : bv 5) (SOff 2 0) sp UO2').
assert (Q3 : getr (ms_regs msc) 3 = w64 (bv_unsigned (getr regs 3)))
  by (vrd_regv HS (3%bv : bv 5) (SOff 3 0) (bv_unsigned (getr regs 3)) UO3').
assert (Q4 : getr (ms_regs msc) 4 = w64 (bv_unsigned (getr regs 4)))
  by (vrd_regv HS (4%bv : bv 5) (SOff 4 0) (bv_unsigned (getr regs 4)) UO4').
unfold w64 in Q3, Q4. rewrite Z_to_bv_bv_unsigned in Q3, Q4. rewrite Rgp in Q3. rewrite Rtp in Q4.
assert (Q1 : getr (ms_regs msc) 1 = Z_to_bv 64 (BASE + vrd_row 299)).
{ first [ pose proof (st_ok_restrict_reg segs _ _ _ _ (1%bv : bv 5) HS) as QQ1
        | pose proof (st_ok_pi_restrict_reg _ _ _ _ (1%bv : bv 5) HS) as QQ1 ].
  lazymatch type of QQ1 with _ = sv_denot _ ?t =>
    replace t with (SOff A_TEXT (vrd_row 299)) in QQ1 by (vm_compute; reflexivity) end.
  rewrite (codeptr_val (PI := PI_prog_A) _ _ HEI2) in QQ1. exact QQ1. }
assert (HspT : spZ (ms_regs msc) = sp) by (unfold spZ; rewrite Q2; unfold w64; apply unsigned_lit_small; lia).
(* the NUL, the token and the GOT guard at the call *)
assert (VNUL : val_mem segs (rdW W (ms_mem msc)) (res + n) 1 0).
{ vrd_valg HS 34%nat 0.
  - cbn [base_val]. rewrite U34'. lia.
  - first [reflexivity | apply vrd_sv_eq; rewrite ?U_SLit; reflexivity | vm_compute; reflexivity].
  - cbn. lia.
  - cbn. lia. }
assert (GARR : garr8 segs (rdW W (ms_mem msc)) res (txt ++ [0])).
{ apply vrd_garr8_snoc.
  - apply (vrd_garr8_keep (w_H W) mem (ms_mem msc)); [|exact GT]. intros j Hj. apply KEEPT; lia.
  - rewrite Hlen. exact VNUL. }
assert (SITE : strtod_site_x segs strtod_img_A W (ms_mem msc) res (fr + 32) txt).
{ split; [first [exact Hgr | rewrite Hlen; exact Hgr]|]. split; [exact Hge|]. split; [lia|]. split.
  - intros a Ha. rewrite KEEPT by lia. exact (GOT a Ha).
  - exact (PMN _ HPM). }
pmkst HS. rewrite vrd_strtod_pc.
eapply SRr_bind.
{ exact (vrd_strtod_row B ARx SK LAWS B_tp B_errno B_errno_own W (ms_regs msc) (ms_mem msc)
    (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)] ly S Hp mdc k
    res (fr + 32) txt (sp - (spZ regs0 + e)) (Z_to_bv 64 (BASE + vrd_row 299)) HJ Q10 Q11
    ltac:(rewrite HspT; lia) Ho16 ltac:(lia) ltac:(lia) Q3 Q4 Q1
    ltac:(apply (ret_ok_codeptr_v (PI := PI_prog_A)); [unfold vrd_row; lia | reflexivity])
    GARR TXT ltac:(lia) ltac:(lia) ltac:(left; lia) HEW ltac:(left; lia) ltac:(lia) FRM SITE). }
(* the row's post ends with memnorm of the memory after the call (YStrtodRowX's additive last conjunct,
   aj_memnorm mem2, the body of YAkMemnorm.memnorm by conversion): srr_inv_call carries P across the call *)
cbv beta. intros W2 c2 _ (-> & fx' & regs2 & mem2 & md2 & bits & c & -> & FZ & FK & FA & SC & Hc0 & HJ2 & HP2 & VM
  & HFR2 & HPR2 & HMN2).
pose proof (PCALL (ms_mem msc) mem2 (fun _ => HMN2) HPM) as HPM2.
replace (spZ regs0 + e + (sp - (spZ regs0 + e))) with sp in HFR2 by lia.
assert (KEEP2 : forall a, 0 <= a < 2 ^ 64 -> ~ (res + n <= a < res + n + 1) -> ~ (fr + 32 <= a < fr + 40) ->
          ~ (sp - STK_RT_STRTOD <= a < sp) -> ~ (as_errno B <= a < as_errno B + 4) ->
          aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
  by (intros a Ha H1 H2 H3 H4; rewrite (HFR2 a Ha ltac:(lia) H3 H4); exact (KEEPT a Ha H1)).
assert (KS2 : forall s, SHADOW_OFF <= s < kHighShadowEnd -> aview segs (w_H W) mem2 s = aview segs (w_H W) mem s).
{ intros s Hs. unfold amem_range, kLowMemEnd, kHighMemBeg, kHighMemEnd in Amres, Ame. apply KEEP2; slia. }
replace (mkCfg (@YK11.mkst fx' regs2 (Z_to_bv 64 (BASE + vrd_row 299)) mem2 (seg_rom segs)) md2)
  with (cfg_at (fx := fx') segs (BASE + vrd_row 299) regs2 mem2 md2) by (unfold cfg_at, w64; reflexivity).
apply (HNXT fx' regs2 mem2 md2 bits c FZ FK FA SC ltac:(lia) HJ2 HPM2).
+ apply (vrd_tk_trans regs2 (ms_regs msc) regs); [apply vrd_tk_pres; exact HP2 |].
  vrd_tkr_a HS HAE2.
+ rewrite (HP2 25) by (unfold acallee_saved; lia). vrd_regv HS (Z_to_bv 5 25) (SOff 26 32) (fr + 32) UO2632'.
+ exact KEEP2.
+ apply (vrd_mg_trans _ (rdW W (ms_mem msc))); [exact MGT | apply vrd_mg_of_pres; exact HPR2].
+ exact VM.
+ apply (vrd_garr8_keep (w_H W) (ms_mem msc) mem2); [|exact GARR].
  intros j Hj. rewrite length_app in Hj. cbn [length] in Hj. apply HFR2; lia.
+ apply (vrd_ra_shkeep (w_H W) (w_H W) mem mem2); [lia | lia | exact KS2 | exact RAv].
+ apply (vrd_ra_shkeep (w_H W) (w_H W) mem mem2); [lia | lia | exact KS2 | exact RAq].
+ apply (vrd_ra_shkeep (w_H W) (w_H W) mem mem2); [lia | lia | exact KS2 | exact RAres].
Qed.

(* ---- THE BOUNDARY AT ROW 299 (A 0x863b4), what vrd_seg_284_P delivers and lane WalkNumEnd (rows 299..328,
   lib/A/VrdNumEnd.v) consumes. pc = row 299 (`addi a1, s3, 8`), AT STRTOD'S FLOAT STATE fx2 (frm_zero, fs0-fs11
   kept against parse_value's entry fx). The state is stated RELATIVE TO THE DISPATCH STATE, as vrd_num266_a is:
   VrdPro.vrd_disp_body at the number arm with its witnesses named (its world Wd and memory mem1 are the dispatch
   ones; no later row changes them), the call's own premises at parse_value's entry, the token rows 163..208
   accepted, the allocator's SUCCESS arm for the block res of |txt| + 1 bytes WITH ITS LEDGER AT THE CURRENT
   MEMORY, the journal from parse_value's entry to the current state, and the machine facts rows 267..298 leave:
   the registers (s5 still -1, s6 = p' + |txt|, s9 = the endptr cell fr + 32, s3 / s4 / s7 / s11 as the dispatch
   left them), the node's str word holding res, the token and its NUL in the block, strtod's answer at fr + 32 and
   in fa0, the frame and the saved words, the caller window, and the three shadow ranges the tail's rows read.
   Rows 299..328 make no call, so no chain and no arodata premise is carried. ---- *)
Definition vrd_num299_a
  (ly0 : alayout) (S0 : astate) (Hp0 : list Z) (W0 : world segs) (regs0 : bvmap 5 word)
  (mem0 : word -> option byte) (md0 : Model) (ch : list (Z * Z * Z)) (CTX0 : list (list Z)) (CW : list (list Z))
  (e q v text len p : Z) (d : nat) (tb : list Z)
  (Lam : list (Z * Z)) (peak cnt fail ran most own : Z)
  : world segs -> config -> Prop :=
  fun W c =>
  exists (fx2 : YK11.FPState) (Wd : world segs) (pos p' k1 k : Z)
         (ly ly2 : alayout) (S S2 : astate) (Hp Hp2 : list Z)
         (regs1 : bvmap 5 word) (mem1 : word -> option byte) (md1 : Model)
         (regs : bvmap 5 word) (mem : word -> option byte) (md : Model)
         (txt r : list Z) (res bits cc sp fr : Z),
  (* the pc, at strtod's float state *)
  c = cfg_at (fx := fx2) segs (BASE + vrd_row 299) regs mem md /\
  frm_zero (@YK11.fp_csr fx2) /\ fregs_kept_x fx fx2 /\
  (* the call's own premises, at parse_value's entry *)
  fpre B ARx (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 md0 ch /\
  getr regs0 10 = w64 q /\ getr regs0 11 = w64 v /\
  rd_pre B (STK_parse_value d) ly0 S0 Hp0 W0 regs0 mem0 Lam peak cnt fail ran most own e q text len p d tb v /\
  (* the dispatch state, at its own world Wd and memory mem1 *)
  vrd_disp_body B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    VA_num pos p' k1 ly S Hp Wd regs1 mem1 md1 /\
  (* the token rows 163..208 accepted, and the rest after it *)
  vrd_num_tok (rest_atR tb text p') = Some (txt, r) /\
  rest_atR tb text (p' + Z.of_nat (length txt)) = r /\
  (* the allocator's SUCCESS arm (prh_alloc_post's third arm at n = |txt| + 1), its ledger AT THE CURRENT memory *)
  cnt <> fail /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\ ~ In res (map fst Lam) /\
  Hp2 = (res - cf_head) :: Hp /\
  ablocks B ly2 S2 = ablocks B ly S ++ [(res - cf_head, Z.of_nat (length txt) + 1 + cf_head)] /\
  room_live_cf S2 /\
  (* THE HULL USE from the ENTRY state S0 to S2, at the arm's own event list (the granted row-270 malloc's one event;
     rows 299..328 move no allocator state): fuzz_malloc's hull use across the fake-frame take, which keeps st_secs *)
  PresetHullBudget.hull_used S0 S2 (PresetReqAt.rd_hevs [EAlloc (Datatypes.S (length txt))]) /\
  prh_ledger B ly2 S2 Hp2 W mem ((res, Z.of_nat (length txt) + 1) :: Lam)
    (Z.max peak (Ledger.lsum Lam + (Z.of_nat (length txt) + 1))) ((cnt + 1) mod 2 ^ 64) fail ran most own /\
  (* the journal from parse_value's entry to the current state, and this call's own frame still live *)
  AJ (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) ly0 S0 Hp0 W0 mem0 md0 [(0, pos)]
     ly2 S2 Hp2 W mem md k /\
  frames S2 = (0, pos) :: frames S0 /\
  (forall a, spZ regs0 <= a < spZ regs0 + e -> ~ inFP (rd_fp q v) a ->
     aview segs (w_H W) mem a = aview segs (w_H W0) mem0 a) /\
  (* strtod's answer: the model's bits in fa0, the consumed length at the endptr cell *)
  vrd_sm txt = Some (bits, cc) /\ 0 <= cc <= Z.of_nat (length txt) /\
  LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fx2) (Z_to_bv 5 10) = Z_to_bv 64 bits /\
  val_mem segs (rdW W mem) (fr + 32) 8 (res + cc) /\
  (* the registers rows 267..298 leave: sp = s1, s0, s2 = s10 = the fake frame, s8 its shadow, s9 the endptr cell *)
  fr = frame_addr ly2 0 pos /\ frame_addr ly 0 pos = fr /\
  getr regs 2 = w64 sp /\ getr regs 9 = w64 sp /\ getr regs 8 = w64 (spZ regs0) /\
  getr regs 18 = w64 fr /\ getr regs 26 = w64 fr /\ getr regs 24 = w64 (SHADOW_OFF + fr / 8) /\
  getr regs (Z_to_bv 5 25) = w64 (fr + 32) /\
  getr regs 19 = w64 v /\ getr regs 20 = w64 q /\ getr regs 23 = w64 SHADOW_OFF /\
  getr regs 27 = w64 (SHADOW_OFF + q / 8) /\
  getr regs 21 = w64 (-1) /\ getr regs 22 = w64 (p' + Z.of_nat (length txt)) /\
  getr regs 3 = getr regs0 3 /\ getr regs 4 = getr regs0 4 /\
  2 ^ 46 <= sp <= 2 ^ 47 - 32 /\ sp mod 32 = 0 /\ sp + 32 <= spZ regs0 - 16 /\
  (* the node, the block and its NUL, the frame's three words and the saved words, at the current memory. NOT
     VrdPro.vrd_frame (a Theorem Labs lane's ruling, option A, 2026-10-29): its shadow conjunct asks granule 4 = 0xf8, but row
     157 (`sb zero, 4(s8)`) zeroes that granule so strtod can store the endptr at fr + 32 and row 327 is the first
     row that writes 0xf8 again; and no boundary from row 157 on states any of the frame's 8 shadow bytes
     (vrd_num266_a's keep excludes them). Rows 299..328 and vrd_epi_a read only the flag word at fr + 56. *)
  val_mem segs (rdW W mem) (v + 16) 8 res /\
  garr8 segs (rdW W mem) res (txt ++ [0]) /\
  val_mem segs (rdW W mem) fr 8 0x41B58AB3 /\ val_mem segs (rdW W mem) (fr + 16) 8 (pa_sigma AS_parse_value) /\
  val_mem segs (rdW W mem) (fr + 56) 8 (flag_addr ly2 0 pos) /\
  vrd_saved (rdW W mem) (spZ regs0) regs0 /\
  (* the shadow the tail's rows read: the node (rows 300..303, 316..318), the cursor (row 322), the block *)
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF v 24 /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF q 8 /\
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF res (Z.of_nat (length txt) + 1) /\
  (* the cursor at the CURRENT view (the dispatch body's conjunct; rows 157..298 write no cursor byte) *)
  pj_in_okR segs (rdW W mem) q text len p' (Z.of_nat d) tb /\
  (* the node, writable and still zero outside its str word: row 276 is the only row that writes it *)
  pj_rwR segs (rdW W mem) v /\
  (forall a, v <= a < v + 56 -> ~ (v + 16 <= a < v + 24) -> aview segs (w_H W) mem a = Some 0) /\
  (* THE POSITION TRANSFER and THE LIVE SET from the ENTRY state S0 to S2 across the granted row-270 malloc, at the
     arm's own event list rd_hevs [EAlloc (S |txt|)] (vrd_pv_post's two conjuncts at tr = [EAlloc (S |txt|)];
     rows 299..328 move no allocator state): from fuzz_malloc's res <> 0 transfer and prh_alloc_post's append, with
     cf_head = PresetReqAt.HEAD (the Section hypothesis HI_head of Section n) *)
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
     (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
     PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs [EAlloc (Datatypes.S (length txt))]) ->
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length (PresetReqAt.rd_hevs [EAlloc (Datatypes.S (length txt))]))%nat H0 hist' S2) /\
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S0))
       (PresetReqAt.rd_hevs [EAlloc (Datatypes.S (length txt))])) /\
  (* the node's first 16 bytes may be written (rows 305 and 321): prhPv_node's home, as rows 271..276 had it *)
  (forall a, v <= a < v + 16 ->
     awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly2 S2) ly2
       [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly2 a).

End t.

(* ======================================================================================================== *)
(* THE COMPOSITION: vrd_num_tail_P, from the boundary at row 267 to the number arm's join                      *)
(* ======================================================================================================== *)
(* rule 24: no function proved. rule 24: proves no function (kind: segment lemma).
   vrd_num_tail_P composes this file's three segments (vrd_seg_267_P / vrd_seg_271_P / vrd_seg_284_P) with WalkNumEnd's
   end segment (rows 299..328), named here H_num_end in the exact form of a Theorem Labs lane's vrd_num_end_stmt
   (lib/A/VrdNumEnd.v, a working branch 4353090b744, blob 2d633b265fff; VrdNumEnd.v Requires this file, so
   lib/A/VrdNumA.v discharges it with vrd_num_end), every one at the arm's memory invariant P: P of the memory at row
   267 to P of the memory at the join. The old statement vrd_num_tail (no P) is gone with the every-state memnorm
   hypothesis: its strtod row needs memnorm at the call, which only P gives (srr_inv_mn). After the row-270 malloc the
   node / cursor / text / block shadow facts are rebuilt with IelemE's GENERIC after-call lemmas (VrdIStep.vrd_node_ra_at
   / vrd_src_at) at the callee journal vrd_seg_267's continuation exposes. The malloc's NULL arm is the only model
   step: the token present, the oracle's first answer false, tr = [EFail (|txt| + 1)], D = [], the ledger moved by
   a Theorem Labs lane's
   VrdLedgerEv.vle_fail_chosen / vle_fail_refused, pj_fdR by VrdNum.vrd_zero_fd, then VrdRefJoinP.vrd_ref_join_P with
   VrdNum.vrd_pv_post_sh_frame. THE POSITION (post-implication text, kit 3ac20a5c9e30): there is no entry position;
   vrd_pv_post's transfer and outcome clauses are proved from fuzz_malloc's own post (its two transfers and its
   OUTCOME clause, which refutes the NULL arm at a consumer HMal with cnt <> fail) and the instance fact
   cf_head = PresetReqAt.HEAD (Section n's HI_head); the row-270 call's sec_cnt / ccnt24 premises come from the
   text's position-free live counts that vrd_disp_body carries (PresetRun.pkR_prefix at the first state), not from
   PresetCfnA.counts_of_room_pos_rl. THE HULL (lib/Spec/PresetHullBudget.v): the text's entry budget at S0 is for the
   granted trace, the one event HMal (|txt| + 1 + cf_head), so it pays the row-270 call's budget across the fake-frame
   take (hull_budget_same: st_secs kept); the call's hull use is vrd_pv_post's at both exits (hull_used_app after
   hull_used_secs). The Requires below come after Section t so that no name the segment proofs above resolve
   changes. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRoomPos PresetRoomPosKeep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import VrdFrame VrdIElem VrdIStep VrdLedgerEv
VrdRefJoinP.

(* ---- the token, pure ---- *)
Lemma vnt_span : forall z a r, span numch z = (a, r) -> z = a ++ r /\ Forall (fun c => numch c = true) a.
Proof.
induction z as [|b z IH]; intros a r H; cbn [span] in H.
- injection H as <- <-. split; [reflexivity | constructor].
- destruct (numch b) eqn:Eb.
  + destruct (span numch z) as [a' r'] eqn:E. injection H as <- <-.
    destruct (IH a' r' eq_refl) as (H1 & H2). subst z. split; [reflexivity | constructor; assumption].
  + injection H as <- <-. split; [reflexivity | constructor].
Qed.

Lemma vnt_tok : forall x txt r, vrd_num_tok x = Some (txt, r) ->
  x = txt ++ r /\ Forall (fun c => numch c = true) txt /\ (1 <= length txt)%nat.
Proof.
intros x txt r H. unfold vrd_num_tok in H.
set (j := match x with b :: _ => vrd_j b | [] => 0%nat end) in H.
assert (Hj : Forall (fun c => numch c = true) (firstn j x)).
{ unfold j, vrd_j. destruct x as [|b x']; [constructor|].
  destruct (b =? 45) eqn:E; cbn [firstn]; [|constructor].
  apply Z.eqb_eq in E. subst b. constructor; [reflexivity | constructor]. }
destruct (skipn j x) as [|c z] eqn:Es; [discriminate|].
destruct (negb (digit c)) eqn:Ed; [discriminate|].
destruct (_ && _); [discriminate|].
destruct (span numch z) as [a r'] eqn:Esp. injection H as <- <-.
destruct (vnt_span z a r' Esp) as (Z1 & Z2).
apply negb_false_iff in Ed.
split; [|split].
- rewrite <- (firstn_skipn j x) at 1. rewrite Es, Z1. rewrite <- app_assoc. reflexivity.
- apply Forall_app. split; [exact Hj|]. constructor; [|exact Z2]. unfold numch. rewrite Ed. reflexivity.
- rewrite length_app. cbn [length]. lia.
Qed.

Lemma vnt_mr_cons_ge : forall b X c, (PjRoundTrip.mr 0 X <= PjRoundTrip.mr c (b :: X))%nat.
Proof.
intros b X c. cbn [PjRoundTrip.mr]. destruct (numch b); [apply PjRoundTrip.mr_mono; lia | lia].
Qed.
Lemma vnt_mr_app_ge : forall l X c, (PjRoundTrip.mr 0 X <= PjRoundTrip.mr c (l ++ X))%nat.
Proof.
induction l as [|b l IH]; intros X c; cbn [app]; [apply PjRoundTrip.mr_mono; lia|].
pose proof (IH X 0%nat). pose proof (vnt_mr_cons_ge b (l ++ X) c). lia.
Qed.
Lemma vnt_mr_run : forall t X c, Forall (fun b => numch b = true) t -> (c + length t <= PjRoundTrip.mr c (t ++ X))%nat.
Proof.
induction t as [|b t IH]; intros X c H; cbn [app length]; [pose proof (PjRoundTrip.mr_ge X c); lia|].
inversion H as [|b' t' Hb Ht]; subst. cbn [PjRoundTrip.mr]. rewrite Hb. specialize (IH X (S c) Ht). lia.
Qed.
Lemma vnt_maxrun : forall (tb : list Z) k txt r, skipn k tb = txt ++ r -> Forall (fun c => numch c = true) txt ->
  (length txt <= PjRoundTrip.maxrun tb)%nat.
Proof.
intros tb k txt r H Hf. unfold PjRoundTrip.maxrun. rewrite <- (firstn_skipn k tb), H.
pose proof (vnt_mr_app_ge (firstn k tb) (txt ++ r) 0) as A. pose proof (vnt_mr_run txt r 0 Hf) as Bm. lia.
Qed.

(* the number arm's model, at the token: the granted trace and the refused run (ok = [false]) *)
Lemma vnt_jv : forall sm d x b y txt r ok,
  PjGrammar.skip x = b :: y -> vrd_arm_of b = VA_num -> vrd_num_tok (b :: y) = Some (txt, r) ->
  jr_value sm d x ok =
    (let (ok0, ok1) := take ok in
     if ok0
     then (if whole sm txt
           then (Some (JNum txt (snd (sm txt)), r), [EAlloc (S (length txt))], ok1)
           else (None, [EAlloc (S (length txt))], ok1))
     else (None, [EFail (S (length txt))], ok1)).
Proof.
intros sm d x b y txt r ok Esk Harm Htok.
assert (N6 : b <> 123 /\ b <> 91 /\ b <> 34 /\ b <> 116 /\ b <> 102 /\ b <> 110).
{ unfold vrd_arm_of in Harm. repeat split; intros Hb; subst b; cbn in Harm; discriminate Harm. }
destruct N6 as (N1 & N2 & N3 & N4 & N5 & N6).
rewrite (vrd_jr_value_number sm d x b y ok Esk N1 N2 N3 N4 N5 N6).
rewrite vrd_num_tok_spec, Htok. reflexivity.
Qed.

(* a proposition lia does not look inside: the main proof hides the disjunctions it carries, so each lia does
   not case-split on all of them (measured: 156 s for one lia before) *)
Definition vnt_hide (P : Prop) : Prop := P.
Local Ltac vnt_hidetac H := let T := type of H in change (vnt_hide T) in H.

Section n. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PIm : PrhImg}
  {RL : PrhRoomLive}.
#[local] Notation segs := (@pa_segs _ _ PI_prog_A).
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).
#[local] Notation AJ := (ajournal_x (SK := SK) segs B prh_pst ARx).
#[local] Notation BASE := (@pa_val _ A_prog_listing PI_prog_A A_TEXT).
Context {HL : Z}.
(* Section t's stand-ins, again (each one's owner and reason is stated above in Section t): LAWS, PST_IMG
   (S1ImgA.pst_in_img_A), H_checked_memcpy_xm (__asan_memcpy's text with the memnorm keep; preset's row
   PRowCpy.prow_asan_memcpy_xm_A), B_tp / B_errno / B_errno_own (image facts of B). fuzz_malloc is NOT a stand-in:
   its published text tfuzz_malloc_specX is a premise of vrd_num_tail_P, as of vrd_num_a_stmt_P. There is NO memnorm
   stand-in: memnorm reaches the strtod row through the generic invariant P (srr_inv_mn), never from a claim about
   every allocator state. *)
Hypothesis LAWS : AR_laws_x segs B ARx HL.
Hypothesis PST_IMG : forall a, Exists (in_zr a) prh_pst -> in_img segs a.
Hypothesis H_checked_memcpy_xm : aintrin_realizes_xm segs B ARx OCpy (pa_sigma AS___asan_memcpy).
Hypothesis B_tp : as_tp B = STRTOD_TP.
Hypothesis B_errno : as_errno B = STRTOD_ERRNO.
Hypothesis B_errno_own : forall a, as_errno B <= a < as_errno B + 4 -> ~ Exists (in_zr a) (as_owned_static B).
(* NEW STAND-INS of the composition, each a fact of the instance or of B:
   - H_HL / H_zsal / H_imgvis / H_pst_ro: IelemE's four (VrdIStep.vrd_node_ra_at / vrd_src_at take them): the head
     bound of AR_laws_x's hshadow law is cf_head, the zero-shadow ranges are granule-aligned, the image's shadow is
     visible, and alloc.c's statics are not read-only
   - HW: the kit's prh_head_wide (a Theorem Labs lane's preset_head_wide, lib/A/CfParamsPreset.v:95, at the instance)
   - H_pv_frame: parse_value's frame is at least 176 bytes (PRH_Img.v gives 176 at the instance; the call budgets
     STK_fuzz_malloc / STK_RT_STRTOD + the frame <= STK_parse_value d)
   - PST_ERRNO: alloc.c's statics miss errno (strtod writes errno before the ledger is read again; at A the statics
     are 0x5dd5c0..0x5dd568 and errno is 0x5dde4c)
   - B_got_const: the strtod GOT guard word is one of B's const cells (S8aNumber.v's HGOTC, verbatim; at the instance
     S8aNumberW.w_hgotc, from AE22.canary_cell_in). It REPLACES the earlier B_got_own (the guard is no owned static of
     B), which is FALSE at image A: Tfib_owned_static holds (0xa2c98, 8), the guard itself (A2NumP's check-2 reviewer;
     AF0m.v:1784). The guard's view at row 271 now comes from AR_laws_x's const-cell law, as S8aNumC.v does. *)
Hypothesis H_HL : HL = cf_head.
Hypothesis H_zsal : Forall (fun r => fst r mod 8 = 0 /\ snd r mod 8 = 0) (as_zero_shadow B).
Hypothesis H_imgvis : forall ly S Hp W mem md a, ARx ly S Hp W mem md -> IMG_LO <= a < IMG_TOP ->
  aview segs (w_H W) mem (shadow_addr a) <> None.
Hypothesis H_pst_ro : forall a, Exists (in_zr a) prh_pst -> ~ in_roP segs pa_relro_lo pa_relro_hi a.
Hypothesis HW : prh_head_wide.
Hypothesis H_pv_frame : 176 <= pi_frame F_parse_value.
Hypothesis PST_ERRNO : forall a, Exists (in_zr a) prh_pst -> ~ (as_errno B <= a < as_errno B + 4).
Hypothesis B_got_const : forall ly, In (z8 (ANum STRTOD_GOT_GUARD) STRTOD_GUARD) (as_const B ly).
(* INSTANCE FACT, one name across the slice (a Theorem Labs lane's ruling, 2026-10-29 ~23:0xZ): the harness head the
   allocator instance hides is the model's HEAD, so the row-270 call's event HMal (|txt| + 1 + cf_head) IS the
   model's rd_hevs [EAlloc (S |txt|)]. Discharged at the unit's top by `reflexivity` at
   CfParamsPreset.CfParams_preset (cf_head = 16 = PresetReqAt.HEAD). *)
Hypothesis HI_head : cf_head = PresetReqAt.HEAD.
(* WalkNumEnd's end segment (rows 299..328), VERBATIM a Theorem Labs lane's vrd_num_end_stmt (lib/A/VrdNumEnd.v blob
   2d633b265fff at a working branch 4353090b744). VrdNumEnd.v Requires this file, so the citation is made
   in lib/A/VrdNumA.v: H_num_end := vrd_num_end. vrd_num_tail_P uses it at its own P. *)
Hypothesis H_num_end : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P ->
  forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    (W : world segs) (c : config),
  vrd_num299_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
    W c ->
  P (ms_mem (cfg_ms c)) ->
  SRr segs W c
    (fun W' c' => (exists (fx2 : YK11.FPState) (pos rv : Z),
       vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
         (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv)
         W' c') /\ P (ms_mem (cfg_ms c'))).

(* ---- where the node lives: a live allocator block (a harness block's user bytes or another block) or a live fake
   frame; the real-stack window is excluded by rd_pre ---- *)
Lemma vnt_node_home : forall ly S Hp W mem md Lam peak cnt fail ran most own regs0 e v,
  ARx ly S Hp W mem md -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  prhReader_at B ly S Lam regs0 e v 56 -> (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v) ->
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= v /\ v + 56 <= b + req_size m /\
     (forall a k, In (a, k) Lam -> (b, m) = (a - cf_head, k + cf_head) -> a <= v)) \/
  (exists cid pos, In (cid, pos) (frames S) /\
     frame_addr ly cid pos <= v /\ v + 56 <= frame_addr ly cid pos + fs_frame_bytes cid).
Proof.
intros ly S Hp W mem md Lam peak cnt fail ran most own regs0 e v HAR HLED Hat Hvw.
destruct Hat as [(a0 & k0 & Hin & Ha & Hk) | [(b & m & Hin & Hnl & Hb & Hm) | [(cid & pos & Hin & H1 & H2) | Hww]]].
- destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLED Hin) as (Hk0 & Hab & _).
  left. exists (a0 - cf_head), (k0 + cf_head). pose proof (@cf_head_nonneg cp) as Hcf.
  split; [exact Hab|]. split; [lia|].
  split; [unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia|].
  intros a k _ E. injection E as E1 _. lia.
- left. exists b, m. split; [exact Hin|]. split; [lia|].
  split; [unfold req_size; destruct (Z.eqb_spec m 0); lia|].
  intros a k HinL E. injection E as E1 E2. exfalso. apply Hnl.
  replace (b + cf_head) with a by lia. replace (m - cf_head) with k by lia. exact HinL.
- right. exists cid, pos. auto.
- exfalso. lia.
Qed.

(* a byte of an allocator block is no head byte of another live harness block, nor of its own unless below its
   user bytes *)
Lemma vnt_head_off : forall ly S Hp W mem md b m a k i x,
  ARx ly S Hp W mem md -> In (b, m) (ablocks B ly S) -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
  0 <= k -> 0 <= i < 8 -> b <= x < b + req_size m -> ((b, m) = (a - cf_head, k + cf_head) -> a <= x) ->
  x <> a - cf_head + i.
Proof.
intros ly S Hp W mem md b m a k i x HAR Hb Ha Hk Hi Hx Heq Hxe. pose proof HW as HW8. unfold prh_head_wide in HW8.
assert (Hd : {(b, m) = (a - cf_head, k + cf_head)} + {(b, m) <> (a - cf_head, k + cf_head)})
  by (decide equality; apply Z.eq_dec).
destruct Hd as [E | Ne]; [pose proof (Heq E); lia|].
pose proof (sep_blocks_x segs B ARx LAWS _ _ _ _ _ _ b m _ _ HAR Hb Ha Ne) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. unfold req_size in *.
destruct (Z.eqb_spec m 0); destruct (Z.eqb_spec (k + cf_head) 0); lia.
Qed.

(* a byte of a live frame is no head byte of a live harness block *)
Lemma vnt_head_off_frame : forall ly S Hp W mem md cid pos a k i x,
  ARx ly S Hp W mem md -> In (cid, pos) (frames S) -> In (a - cf_head, k + cf_head) (ablocks B ly S) ->
  0 <= k -> 0 <= i < 8 -> frame_addr ly cid pos <= x < frame_addr ly cid pos + fs_frame_bytes cid ->
  x <> a - cf_head + i.
Proof.
intros ly S Hp W mem md cid pos a k i x HAR Hf Ha Hk Hi Hx Hxe. pose proof HW as HW8. unfold prh_head_wide in HW8.
pose proof (sep_block_frame_x segs B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Ha Hf) as Hdj.
unfold zdisjoint in Hdj. cbn [fst snd] in Hdj. unfold req_size in *.
destruct (Z.eqb_spec (k + cf_head) 0); lia.
Qed.

(* the ledger survives a change confined to a set X of bytes that holds no image byte and no head byte of its
   blocks: the statics are image bytes (PST_IMG), the heads the 8 bytes at each harness block's base *)
Lemma vnt_ledger_keep : forall ly S Hp W mem mem' memX mdX Lam peak cnt fail ran most own (X : Z -> Prop),
  ARx ly S Hp W memX mdX -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, X a -> ~ in_img segs a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 -> ~ X (a - cf_head + i)) ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' memX mdX Lam peak cnt fail ran most own X HAR HLD HK HXi HXh.
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HW as HW8. unfold prh_head_wide in HW8.
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran most own HLD).
- intros a Ha. pose proof (PST_IMG a Ha) as Hi. pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hl.
  apply HK; [unfold kLowMemEnd in *; lia | intros HX; exact (HXi a HX Hi)].
- intros a k i Hin Hi.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLD Hin) as (Hk0 & Hab & _).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W memX mdX _ _ HAR Hab) as (_ & H4096 & Hc & _).
  assert (Hrq : 8 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  apply HK; [lia | exact (HXh a k i Hin Hi)].
- intros a k _ H. exact H.
- apply Permutation_refl.
Qed.

(* two views that hold the same value at a range agree on its bytes *)
Lemma vnt_vm_same : forall (H H' : word -> bool) (m m' : word -> option byte) a (n : nat) v x,
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v -> a <= x < a + Z.of_nat n ->
  aview segs H m x = aview segs H' m' x.
Proof.
intros H H' m m' a n v x H1 H2 Hx. unfold aview.
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (H1 (Z.to_nat (x - a)) ltac:(lia)), (H2 (Z.to_nat (x - a)) ltac:(lia)). reflexivity.
Qed.

(* the recursion's stack bound covers the callees' needs below parse_value's own frame *)
Lemma vnt_stk : forall d,
  pi_frame F_parse_value + LEAF_pv_pi <= STK_parse_value d /\ STK_fuzz_malloc <= LEAF_pv_pi /\
  STK_RT_STRTOD <= LEAF_pv_pi /\ 0 <= STK_fuzz_malloc.
Proof.
intros d. pose proof (pi_frame_nonneg F_parse_value) as H1. pose proof (pi_frame_nonneg F_parse_items) as H2.
pose proof (pi_frame_nonneg F_fuzz_malloc) as H3. pose proof (pi_frame_nonneg F_own) as H4.
assert (L : STK_fuzz_malloc <= LEAF_pv_pi /\ STK_RT_STRTOD <= LEAF_pv_pi).
{ unfold LEAF_pv_pi, zmaxl. cbn [fold_right]. lia. }
assert (L0 : 0 <= STK_fuzz_malloc).
{ unfold STK_fuzz_malloc, zmaxl, STK_RT_ALLOC, STK_RT_ECALL, STK_own. cbn [fold_right].
  unfold ASTACK, ESTACK. lia. }
split; [|tauto]. unfold STK_parse_value.
assert (Hm : pi_frame F_parse_value + pi_frame F_parse_items <=
             Z.of_nat (S (PjGrammar.MAXD - d)) * (pi_frame F_parse_value + pi_frame F_parse_items)).
{ rewrite Nat2Z.inj_succ. nia. }
lia.
Qed.

(* the last entry of a pairwise list is related to every earlier one *)
Lemma vnt_pw_last : forall {X : Type} (R : X -> X -> Prop) (l : list X) x, pairwise R (l ++ [x]) ->
  forall y, In y l -> R y x.
Proof.
intros X R l. induction l as [|z l IH]; intros x H y Hy; [destruct Hy|].
cbn [app pairwise] in H. destruct H as (HF & HP). destruct Hy as [<- | Hy].
- rewrite Forall_forall in HF. apply HF. apply in_or_app. right. left. reflexivity.
- exact (IH x HP y Hy).
Qed.

(* the block an allocation appended is fresh. The kit's PRH_FnAlloc.prh_alloc_fresh_append states the same from the
   append equality and NoDup of the block BASES; no ARx law states that every block's size is nonnegative, which NoDup
   of the bases needs, so this derives it as that lemma does, from the blocks law's pairwise disjointness at the post
   state, using only that the NEW block is not empty *)
Lemma vnt_fresh : forall ly S ly' S' Hp' W' mem' md' res k, 0 <= k ->
  ARx ly' S' Hp' W' mem' md' -> ablocks B ly' S' = ablocks B ly S ++ [(res - cf_head, k + cf_head)] ->
  ~ In (res - cf_head, k + cf_head) (ablocks B ly S).
Proof.
intros ly S ly' S' Hp' W' mem' md' res k Hk HAR E Hin.
destruct (alx_blocks segs B ARx LAWS ly' S' Hp' W' mem' md' (res - cf_head) (k + cf_head) HAR
  ltac:(rewrite E; apply in_or_app; right; left; reflexivity)) as (_ & _ & _ & _ & _ & Hpw).
rewrite E, map_app in Hpw. cbn [map] in Hpw.
pose proof (vnt_pw_last zdisjoint _ _ Hpw _ (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ Hin)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. unfold req_size in Hd. pose proof (@cf_head_nonneg cp) as Hcf.
destruct (Z.eqb_spec (k + cf_head) 0); lia.
Qed.

(* a byte of a text the reader reads is a byte of a live allocator block or an image byte (prhReader_home) *)
Lemma vnt_text_where : forall ly S Hp W mem Lam peak cnt fail ran most own p n x,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prhReader_home B ly S Hp Lam p n -> p <= x < p + n ->
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= x < b + req_size m) \/ in_img segs x.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own p n x HLD
  [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] | (b & m & Hin & Hnh & Hb & Hm)] Hx.
- left. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ b m _ _ HLD Hin) as (Hm0 & Hab & _).
  pose proof (@cf_head_nonneg cp) as Hcf.
  exists (b - cf_head), (m + cf_head). split; [exact Hab|].
  unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia.
- right. destruct (Hro x Hx) as (Hr & _). exact (vrd_ro_img _ Hr).
- right. destruct (Hro x Hx) as (Hr & _). exact (vrd_ro_img _ Hr).
- left. exists b, m. split; [exact Hin|]. unfold req_size; destruct (Z.eqb_spec m 0); lia.
Qed.

(* an addressable range misses the frame's eight poisoned shadow bytes (RESTATED from VnumD's
   VrdNumScan.vrd_ra_off_frame, which this file cannot Require: VrdNumScan.v Requires VrdNumTail.v) *)
Lemma vnt_ra_off_frame : forall (rd : Z -> option Z) a n F,
  range_addressable rd SHADOW_OFF a n ->
  (forall i, 0 <= i < 8 -> rd (SHADOW_OFF + F / 8 + i) = Some (nth (Z.to_nat i) vrd_frame_shadow 0)) ->
  forall x, a <= x < a + n -> ~ (SHADOW_OFF + F / 8 <= shadow_of_addr SHADOW_OFF x < SHADOW_OFF + F / 8 + 8).
Proof.
intros rd a n F Hra HF x Hx Hin.
destruct (Hra x Hx) as (s & Hs & Hok).
set (i := shadow_of_addr SHADOW_OFF x - (SHADOW_OFF + F / 8)).
assert (Hi : 0 <= i < 8) by (unfold i; lia).
replace (shadow_of_addr SHADOW_OFF x) with (SHADOW_OFF + F / 8 + i) in Hs by (unfold i; lia).
assert (Hc : 8 <= nth (Z.to_nat i) vrd_frame_shadow 0).
{ clear - Hi. assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7) as Hi8 by lia.
  destruct Hi8 as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; unfold vrd_frame_shadow; simpl; lia. }
assert (Hs8 : 8 <= s) by (rewrite (HF i Hi) in Hs; injection Hs as Es; rewrite <- Es; exact Hc).
unfold saddr_ok in Hok. destruct Hok as [Hok | (_ & Hok)]; lia.
Qed.

(* addressability moves with the shadow bytes it reads *)
Lemma vnt_ra_keep : forall (rd rd' : Z -> option Z) (Bz a n : Z),
  (forall x, a <= x < a + n -> rd' (shadow_of_addr Bz x) = rd (shadow_of_addr Bz x)) ->
  range_addressable rd Bz a n -> range_addressable rd' Bz a n.
Proof. intros rd rd' Bz a n HK H x Hx. destruct (H x Hx) as (s & Hs & Ho). exists s. rewrite HK by exact Hx. auto. Qed.

(* a byte a value is read from is visible *)
Lemma vnt_vm_some : forall (H : word -> bool) (m : word -> option byte) a (n : nat) v x,
  val_mem segs (mrestrict H m) a n v -> a <= x < a + Z.of_nat n -> aview segs H m x <> None.
Proof.
intros H m a n v x Hv Hx. unfold aview. replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (Hv (Z.to_nat (x - a)) ltac:(lia)). discriminate.
Qed.

(* two nonempty ranges whose bytes are pairwise apart lie apart *)
Lemma vnt_interval : forall a m b k, 0 < m -> 0 < k ->
  (forall x, a <= x < a + m -> ~ (b <= x < b + k)) -> a + m <= b \/ b + k <= a.
Proof.
intros a m b k Hm Hk H. destruct (Z_le_gt_dec (a + m) b) as [E | E]; [left; exact E|].
destruct (Z_le_gt_dec (b + k) a) as [E' | E']; [right; exact E'|].
exfalso. apply (H (Z.max a b)); lia.
Qed.

(* a callee-saved register of the state after a call, as the caller left it *)
Local Ltac vnt_cs HPR r R :=
  lazymatch goal with |- getr ?rg ?x = _ =>
    replace x with (Z_to_bv 5 r) by (apply bv_eq; reflexivity);
    rewrite (HPR r ltac:(clear; unfold acallee_saved; lia));
    replace (Z_to_bv 5 r) with x by (apply bv_eq; reflexivity); exact R end.


(* a hull of an application range is a run of shadow bytes inside the shadow band *)
Lemma vnt_hull_rng : forall x n s, 0 <= x -> x + n <= 2 ^ 47 -> 0 < n ->
  shadow_addr x / 8 * 8 <= s < shadow_addr (x + n - 1) / 8 * 8 + 8 -> SHADOW_OFF <= s < SHADOW_OFF + 2 ^ 44 + 8.
Proof.
intros x n s Hx Hxn Hn Hs. unfold shadow_addr in Hs.
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HP47 : (2 : Z) ^ 47 = 140737488355328) by reflexivity.
assert (HP44 : (2 : Z) ^ 44 = 17592186044416) by reflexivity.
assert (A : SHADOW_OFF / 8 <= (SHADOW_OFF + x / 8) / 8)
  by (apply Z.div_le_mono; [lia | pose proof (Z.div_pos x 8 ltac:(lia) ltac:(lia)); lia]).
assert (A' : SHADOW_OFF / 8 * 8 = SHADOW_OFF) by (rewrite HSO; reflexivity).
assert (C : 8 * ((SHADOW_OFF + (x + n - 1) / 8) / 8) <= SHADOW_OFF + (x + n - 1) / 8) by (apply Z.mul_div_le; lia).
assert (D : (x + n - 1) / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; lia).
nia.
Qed.

(* the ledger survives a change confined to a set X of bytes that meets no static and no head byte of its blocks *)
Lemma vnt_ledger_keep_pst : forall ly S Hp W mem mem' memX mdX Lam peak cnt fail ran most own (X : Z -> Prop),
  ARx ly S Hp W memX mdX -> prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ X a -> aview segs (w_H W) mem' a = aview segs (w_H W) mem a) ->
  (forall a, Exists (in_zr a) prh_pst -> ~ X a) ->
  (forall a k i, In (a, k) Lam -> 0 <= i < 8 -> ~ X (a - cf_head + i)) ->
  prh_ledger B ly S Hp W mem' Lam peak cnt fail ran most own.
Proof.
intros ly S Hp W mem mem' memX mdX Lam peak cnt fail ran most own X HAR HLD HK HXp HXh.
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5). pose proof HW as HW8. unfold prh_head_wide in HW8.
apply (prh_ledger_kept_aview B ly S Hp W mem ly S Hp W mem' Lam peak cnt fail ran most own HLD).
- intros a Ha. pose proof (PST_IMG a Ha) as Hi. pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hl.
  apply HK; [unfold kLowMemEnd in *; lia | exact (HXp a Ha)].
- intros a k i Hin Hi.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a k _ _ HLD Hin) as (Hk0 & Hab & _).
  destruct (alx_blocks segs B ARx LAWS ly S Hp W memX mdX _ _ HAR Hab) as (_ & H4096 & Hc & _).
  assert (Hrq : 8 <= req_size (k + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k + cf_head) 0); lia).
  apply HK; [lia | exact (HXh a k i Hin Hi)].
- intros a k _ H. exact H.
- apply Permutation_refl.
Qed.

(* the ledger's bounds the refusal's one-event step takes (the #102 ledger steps also ask 0 <= peak) *)
Lemma vnt_ledger_bounds : forall ly S Hp W mem Lam peak cnt fail ran most own,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own ->
  Ledger.lsum Lam <= peak /\ 0 <= peak /\ 0 <= cnt < 2 ^ 64.
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own (HG & _). unfold prh_glob in HG. decompose [and] HG. lia.
Qed.

(* ---- THE POSITION-TRANSFER AND LIVE-SET STEPS of the post-implication text, from fuzz_malloc's own post (kit
   PRH_FnAlloc.v 95e26ff95e63 :285-306). The live requests are the allocator blocks' sizes (room_of_cf), so they
   read off ablocks; the frame take S = set_fs f S0 keeps both by conversion. cf_head = PresetReqAt.HEAD makes the
   model's event rd_hevs [EAlloc (S k)] the call's HMal (S k + cf_head). ---- *)
Lemma vnt_live_ab : forall ly S, map snd (ablocks B ly S) = PresetRoom.rs_live (YGcfRoom.room_of_cf S).
Proof. intros ly S. unfold ablocks. rewrite map_map. reflexivity. Qed.

Lemma vnt_hevs_alloc : forall k, cf_head = PresetReqAt.HEAD ->
  PresetReqAt.rd_hevs [EAlloc (Datatypes.S k)] = [PresetReqAt.HMal (Z.of_nat k + 1 + cf_head)].
Proof.
intros k HI. unfold PresetReqAt.rd_hevs. cbn [flat_map PresetReqAt.rd_hev app]. rewrite HI. f_equal. f_equal. lia.
Qed.

(* the GRANT: the live set and the position move by the one event *)
Lemma vnt_live_alloc : forall ly S0 f ly2 S2 b k, cf_head = PresetReqAt.HEAD ->
  ablocks B ly2 S2 = ablocks B ly (set_fs f S0) ++ [(b, Z.of_nat k + 1 + cf_head)] ->
  Permutation (PresetRoom.rs_live (YGcfRoom.room_of_cf S2))
    (PresetReqAt.hlive_from (PresetRoom.rs_live (YGcfRoom.room_of_cf S0))
       (PresetReqAt.rd_hevs [EAlloc (Datatypes.S k)])).
Proof.
intros ly S0 f ly2 S2 b k HI HA.
rewrite (vnt_hevs_alloc k HI). rewrite <- (vnt_live_ab ly2 S2), HA, map_app.
change (map snd (ablocks B ly (set_fs f S0))) with (map snd (ablocks B ly S0)). rewrite (vnt_live_ab ly S0).
cbn [map snd PresetReqAt.hlive_from fold_left PresetReqAt.hstep].
apply Permutation_sym, Permutation_cons_append.
Qed.

Lemma vnt_transfer_alloc : forall S0 f S2 k, cf_head = PresetReqAt.HEAD ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
     (i : nat) (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (set_fs f S0) ->
     PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat k + 1 + cf_head)] ->
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length [PresetReqAt.HMal (Z.of_nat k + 1 + cf_head)])%nat H0 hist' S2) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs [EAlloc (Datatypes.S k)]) ->
    exists hist', PresetRoomPos.iface_room_pos sm x os
      (i + length (PresetReqAt.rd_hevs [EAlloc (Datatypes.S k)]))%nat H0 hist' S2.
Proof.
intros S0 f S2 k HI T sm x os i H0 hist HP HR. rewrite (vnt_hevs_alloc k HI) in HR |- *.
exact (T sm x os i H0 hist (PresetRoomPosKeep.room_pos_set_fs sm x os i H0 hist S0 f HP) HR).
Qed.

(* the NULL: no event, the position kept *)
Lemma vnt_transfer_null : forall S0 f S2 k,
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
     (i : nat) (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (set_fs f S0) -> PRH_Base.prh_run_at sm x os i [] ->
     exists hist', PresetRoomPos.iface_room_pos sm x os (i + length (@nil PresetReqAt.hev))%nat H0 hist' S2) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs [EFail k]) ->
    exists hist', PresetRoomPos.iface_room_pos sm x os
      (i + length (PresetReqAt.rd_hevs [EFail k]))%nat H0 hist' S2.
Proof.
intros S0 f S2 k T sm x os i H0 hist HP HR.
exact (T sm x os i H0 hist (PresetRoomPosKeep.room_pos_set_fs sm x os i H0 hist S0 f HP) HR).
Qed.

(* the OUTCOME at the NULL: fuzz_malloc's outcome clause (res <> 0 at a consumer HMal with cnt <> fail) refutes the
   premises of vrd_pv_post's outcome clause when the instance's answer is NULL, so that clause holds of anything *)
Lemma vnt_outcome_null : forall (Pc : Prop) S0 f S2 (res : Z) k cnt fail, cf_head = PresetReqAt.HEAD -> res = 0 ->
  (forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat))
     (i : nat) (H0 : list Z) (hist : list YG00.chunk),
     PresetRoomPos.iface_room_pos sm x os i H0 hist (set_fs f S0) ->
     PRH_Base.prh_run_at sm x os i [PresetReqAt.HMal (Z.of_nat k + 1 + cf_head)] ->
     PRH_Base.prh_cons_from sm x os i (length [PresetReqAt.HMal (Z.of_nat k + 1 + cf_head)]) -> cnt <> fail ->
     res <> 0 /\
     exists hist', PresetRoomPos.iface_room_pos sm x os
       (i + length [PresetReqAt.HMal (Z.of_nat k + 1 + cf_head)])%nat H0 hist' S2) ->
  forall (sm : list Z -> Z * Z) (x : list Z) (os : list (option nat * option nat * option nat)) (i : nat)
    (H0 : list Z) (hist : list YG00.chunk),
    PresetRoomPos.iface_room_pos sm x os i H0 hist S0 ->
    PRH_Base.prh_run_at sm x os i (PresetReqAt.rd_hevs [EAlloc (Datatypes.S k)]) ->
    PRH_Base.prh_cons_from sm x os i (length (PresetReqAt.rd_hevs [EAlloc (Datatypes.S k)])) ->
    (fail < cnt \/ cnt + Z.of_nat (calls [EAlloc (Datatypes.S k)]) <= fail) -> Pc.
Proof.
intros Pc S0 f S2 res k cnt fail HI Hr OC sm x os i H0 hist HP HR HC HF.
rewrite (vnt_hevs_alloc k HI) in HR, HC.
assert (Hne : cnt <> fail) by (cbn [calls is_call Nat.add Z.of_nat] in HF; lia).
destruct (OC sm x os i H0 hist (PresetRoomPosKeep.room_pos_set_fs sm x os i H0 hist S0 f HP) HR HC Hne) as [Hn _].
contradiction.
Qed.

(* a byte read as zero *)
Lemma vnt_zero_bytes : forall (H : word -> bool) (m : word -> option byte) a (n : nat) x,
  val_mem segs (mrestrict H m) a n 0 -> a <= x < a + Z.of_nat n -> aview segs H m x = Some 0.
Proof.
intros H m a n x Hv Hx. unfold aview.
replace x with (a + Z.of_nat (Z.to_nat (x - a))) by lia.
rewrite (Hv (Z.to_nat (x - a)) ltac:(lia)). cbn [option_map]. f_equal.
lazymatch goal with |- context [?f 0%Z ?w ?k] =>
  change (f 0%Z w k) with ((Z.shiftr (0 mod 2 ^ (8 * Z.of_nat w)) (8 * Z.of_nat k)) mod 256) end.
rewrite Zmod_0_l, Z.shiftr_0_l, Zmod_0_l. reflexivity.
Qed.

(* presence from writability off the image (no segment byte there), and from a visible byte off the image *)
Lemma vnt_pres_of_wr : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img segs a -> writable_at segs (mrestrict H m) a -> apresent H m a.
Proof.
intros H m a Ha Hn Hw. assert (Hf : find_segment segs a 1 = None) by (apply find_segment_none; exact Hn).
unfold writable_at, wview, mrestrict in Hw. rewrite unsigned_lit_small in Hw by lia. rewrite Hf in Hw.
unfold apresent.
destruct (H (Z_to_bv 64 a)); [exfalso; apply Hw; reflexivity|]. split; [reflexivity|].
destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply Hw; reflexivity].
Qed.
Lemma vnt_pres_of_view : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img segs a -> aview segs H m a <> None -> apresent H m a.
Proof.
intros H m a Ha Hn Hv. assert (Hr : seg_rom segs (Z_to_bv 64 a) = None) by (apply seg_rom_none; assumption).
unfold aview, mbyte, mrestrict in Hv. cbv beta in Hv. unfold apresent.
destruct (H (Z_to_bv 64 a)); [rewrite Hr in Hv; exfalso; apply Hv; reflexivity|].
split; [reflexivity|]. destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
rewrite Hr in Hv. exfalso. apply Hv. reflexivity.
Qed.

(* writability moves with the visible bytes off the image, or follows from them *)
Lemma vnt_rw_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) a n,
  (forall x, a <= x < a + n -> 0 <= x < 2 ^ 64 /\ ~ in_img segs x) ->
  (forall x, a <= x < a + n -> aview segs H' m' x = aview segs H m x) ->
  rd_rw segs (mrestrict H m) a n -> rd_rw segs (mrestrict H' m') a n.
Proof.
intros H H' m m' a n Hx HK Hrw x Hxr. destruct (Hx x Hxr) as (H64 & Hni).
apply apresent_writable. eapply apresent_transfer; [exact H64 | exact Hni | exact (HK x Hxr) |].
apply vnt_pres_of_wr; [exact H64 | exact Hni | exact (Hrw x Hxr)].
Qed.
Lemma vnt_rw_of_view : forall (H : word -> bool) (m : word -> option byte) a n,
  (forall x, a <= x < a + n -> 0 <= x < 2 ^ 64 /\ ~ in_img segs x /\ aview segs H m x <> None) ->
  rd_rw segs (mrestrict H m) a n.
Proof.
intros H m a n Hx x Hxr. destruct (Hx x Hxr) as (H64 & Hni & Hv).
apply apresent_writable. exact (vnt_pres_of_view H m x H64 Hni Hv).
Qed.

(* a value, and a byte array, moved byte by byte *)
Lemma vnt_vm_move : forall (H H' : word -> bool) (m m' : word -> option byte) a a' (n : nat) v,
  (forall k, (k < n)%nat -> aview segs H' m' (a' + Z.of_nat k) = aview segs H m (a + Z.of_nat k)) ->
  val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a' n v.
Proof.
intros H H' m m' a a' n v HK HV k Hk. pose proof (HK k Hk) as E. pose proof (HV k Hk) as Hb.
unfold aview in E. rewrite Hb in E. cbn [option_map] in E.
destruct (mbyte segs (mrestrict H' m') (a' + Z.of_nat k)) as [b'|] eqn:Eb; cbn [option_map] in E; [|discriminate E].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Lemma vnt_garr8_xfer : forall (H H' : word -> bool) (m m' : word -> option byte) base l,
  (forall x, base <= x < base + Z.of_nat (length l) -> aview segs H' m' x = aview segs H m x) ->
  garr8 segs (mrestrict H m) base l -> garr8 segs (mrestrict H' m') base l.
Proof.
intros H H' m m' base l HK HG j Hj. destruct (HG j Hj) as [HV HR]. split; [|exact HR].
apply (vnt_vm_move H H' m m' (base + Z.of_nat j) (base + Z.of_nat j) 1 (nth j l 0)); [|exact HV].
intros k Hk. apply HK. lia.
Qed.

(* a text byte: a byte of a live allocator block, or a read-only image byte off errno (prhReader_home) *)
Lemma vnt_text_home : forall ly S Hp W mem Lam peak cnt fail ran most own p n x,
  prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own -> prhReader_home B ly S Hp Lam p n -> p <= x < p + n ->
  (exists b m, In (b, m) (ablocks B ly S) /\ b <= x < b + req_size m) \/
  (in_img segs x /\ ~ (as_errno B <= x < as_errno B + 4)).
Proof.
intros ly S Hp W mem Lam peak cnt fail ran most own p n x HLD
  [[(b & m & Hin & Hb & Hm) | [(Hzs & Hlo & Hhi & Hro) | (Hlo & Hhi & Hro)]] | (b & m & Hin & Hnh & Hb & Hm)] Hx.
- left. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ b m _ _ HLD Hin) as (Hm0 & Hab & _).
  pose proof (@cf_head_nonneg cp) as Hcf.
  exists (b - cf_head), (m + cf_head). split; [exact Hab|].
  unfold req_size; destruct (Z.eqb_spec (m + cf_head) 0); lia.
- right. destruct (Hro x Hx) as (Hr & _ & He). split; [exact (vrd_ro_img _ Hr) | exact He].
- right. destruct (Hro x Hx) as (Hr & _ & He & _). split; [exact (vrd_ro_img _ Hr) | exact He].
- left. exists b, m. split; [exact Hin|]. unfold req_size; destruct (Z.eqb_spec m 0); lia.
Qed.

(* a register through kept-register steps and a call *)
Lemma vnt_regs1 : forall (r2 r1 r0 : bvmap 5 word),
  vrd_tk r2 r1 -> (forall r, acallee_saved r -> getr r1 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r)) ->
  forall r, acallee_saved r -> r <> 25 -> getr r2 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r).
Proof. intros r2 r1 r0 T21 P10 r Hr H25. rewrite (T21 r Hr H25). exact (P10 r Hr). Qed.
Lemma vnt_regs2 : forall (r3 r2 r1 r0 : bvmap 5 word),
  vrd_tk r3 r2 -> vrd_tk r2 r1 -> (forall r, acallee_saved r -> getr r1 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r)) ->
  forall r, acallee_saved r -> r <> 25 -> getr r3 (Z_to_bv 5 r) = getr r0 (Z_to_bv 5 r).
Proof. intros r3 r2 r1 r0 T32 T21 P10 r Hr H25. rewrite (T32 r Hr H25), (T21 r Hr H25). exact (P10 r Hr). Qed.
Local Ltac vnt_rg L r R :=
  lazymatch goal with |- getr _ ?x = _ =>
    replace x with (Z_to_bv 5 r) by (apply bv_eq; reflexivity);
    rewrite (L r ltac:(clear; unfold acallee_saved; lia) ltac:(clear; lia));
    replace (Z_to_bv 5 r) with x by (apply bv_eq; reflexivity); exact R end.

(* the image band [0x10000, 0x600000) is covered by segments: its first and its fourth *)
Lemma vnt_img_wit : (exists sg, In sg segs /\ Z.of_N (seg_base sg) <= 0x10000) /\
  (exists sg, In sg segs /\ 0x600000 <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg)).
Proof.
split.
- exists Asan.Asan_segment_000. split; [left; reflexivity | cbn; lia].
- exists Asan.Asan_segment_003. split; [do 3 right; left; reflexivity | cbn; lia].
Qed.

Lemma vrd_num_tail_P : forall (P : (word -> option byte) -> Prop), srr_inv_laws segs P -> srr_inv_call segs P ->
  srr_inv_mn segs P ->
  forall ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own (W : world segs) (c : config),
  tfuzz_malloc_specX B ARx SK ->
  vrd_num266_a B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
    most own W c ->
  PresetHullBudget.hull_budget S0 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) ->
  P (ms_mem (cfg_ms c)) ->
  SRr segs W c (fun W' c' => (exists (fx2 : YK11.FPState) (pos rv : Z),
    vrd_epi_a (fx := fx) B ARx SK fx2 d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos rv
      (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos rv)
      W' c') /\ P (ms_mem (cfg_ms c'))).
Proof.
intros P PLAW PCALL PMN ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran
  most own W c HMAL H266 HBUD HPM.
destruct H266 as (pos & p' & k1 & k & ly & S & Hp & regs1 & mem1 & md1 & regs & mem & md & txt & r & -> & HPRE &
  R10q & R11v & HRD & HB & Htok & Hrest & HJ & HK & HG & HKR & R21 & R22 & V16).
change (P mem) in HPM.
pose proof HB as (HRest & Hpp & HM & HJ1 & HFr & HAB & HHp & HFS & HWIN & HFW & HFRAME & HSAV & HREGS & HCH0 & HUC &
  HCE & HCC & HIN & HRAq & HNODE & HUNIV & Hq0 & Hq1 & Hqv & Rgp0 & Rtp0 & Hret & Hra4 & HIN0 & Hdmax & Htv & Hvw & HU1 & HU2 &
  Hmr & Hcnt & HSRC & HHOME & HLED & HROOM & HPK1 & HPK2 & _ & _ & HFRN & HROD & HFZ & HCWd & HWRd & HCEIL).
pose proof HJ as (HAR & Hly & _ & _ & _ & Hfrs & _ & _ & F1 & F2 & F3 & F4 & _ & Hpres & HSTACK & _).
pose proof HSTACK as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof Hly as (_ & _ & _ & _ & _ & ELF & _ & _ & Etop & Eslo & Eshi & _).
pose proof HPRE as ((HAR0 & _ & _ & _ & _ & HSTK0 & _) & _ & Hhi0).
pose proof HSTK0 as (Hal0 & _ & Hceil0 & Hslo0 & Hshi0 & H470 & _ & Htop0 & Htop20).
pose proof HFW as (He0 & He16 & Hetop & Hepres).
pose proof HREGS as (R2 & R9 & R8 & R18 & R26 & R19 & R20 & R21d & R22d & R25d & R23 & R24 & R27 & R3 & R4 & R10 & R12).
pose proof HKR as (K2 & K3 & K4 & K8 & K9 & K10 & K12 & K18 & K19 & K20 & K23 & K24 & K26 & K27).
pose proof HNODE as (Hv4 & Hv8 & Hrwv & Hzv & Hatv & Hamv & Hownv & Hrav).
pose proof HSRC as (Hbyt & Ht4 & Htc & Hamt & Hrat & Hhut).
pose proof HIN as (Vq & Vq8 & Vq16 & Hrwq & Hq8 & Ht0 & Htl & Hp'r & Hlen & GT & Hqt & Hd32).
pose proof HIN0 as (Vq0 & Vq80 & Vq160 & _ & _ & _ & _ & Hpr0 & _ & _ & _ & _).
change (vnt_hide (q + 24 <= v \/ v + 56 <= q)) in Hqv.
change (vnt_hide (0 < len -> text + len <= v \/ v + 56 <= text)) in Htv.
change (vnt_hide (v + 56 <= spZ regs0 \/ spZ regs0 + e <= v)) in Hvw.
pose proof YCbq.asan_consts as (C1 & C2 & C3 & C4 & C5).
pose proof (vrd_stk_big d) as HSTK. pose proof (vnt_stk d) as (HSTKpv & HSTKfm & HSTKst & HSTKfm0).
pose proof H_pv_frame as HPV.
pose proof (@cf_head_nonneg cp) as Hcf.
pose proof HW as HW8. unfold prh_head_wide in HW8.
assert (HSO : SHADOW_OFF = 2147450880) by reflexivity.
assert (HKLS : kLowShadowBeg = 2147446784) by reflexivity.
assert (HES : ESTACK = 4096) by reflexivity.
assert (HKS : STK_RT_STRTOD = 16384) by reflexivity.
assert (HP46 : (2 : Z) ^ 46 = 70368744177664) by reflexivity.
assert (HP47 : (2 : Z) ^ 47 = 140737488355328) by reflexivity.
assert (HP44 : (2 : Z) ^ 44 = 17592186044416) by reflexivity.
assert (HP62 : (2 : Z) ^ 62 = 4611686018427387904) by reflexivity.
assert (HP64 : (2 : Z) ^ 64 = 18446744073709551616) by reflexivity.
(* the stack: sp = s1 is parse_value's 32-aligned frame base, 160..176 below the entry sp *)
destruct (vrd_A_bounds (spZ regs0) Hal0 ltac:(lia)) as (A1 & A2 & A3). unfold vrd_A in A1, A2, A3.
set (sp := spZ regs1).
assert (HSP : sp = spZ regs0 - 160 - (spZ regs0 - 160) mod 32)
  by (unfold sp; unfold spZ at 1; rewrite R2; unfold w64; apply unsigned_lit_small; lia).
rewrite <- HSP in A1, A2, A3.
(* the fake frame *)
set (fr := frame_addr ly 0 pos).
assert (Hfr : fr = frame_addr ly 0 pos) by reflexivity.
assert (Hsp : sp = spZ regs1) by reflexivity.
assert (HinF : In (0, pos) (frames S)) by (rewrite HFr; left; reflexivity).
destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (HF4 & HFc & HFapp).
assert (Hfb : fs_frame_bytes 0 = 64) by reflexivity. rewrite Hfb in HFc, HFapp.
fold fr in HF4, HFc, HFapp.
assert (HF8 : frame_addr ly 0 pos mod 8 = 0).
{ destruct (alx_frames segs B ARx LAWS ly S Hp W mem md 0 pos HAR HinF) as (H32 & _). clear - H32.
  apply Z.mod_divide in H32; [|lia]. destruct H32 as [a3 E3]. rewrite E3.
  replace (a3 * 32) with ((a3 * 4) * 8) by lia. apply Z.mod_mul. lia. }
assert (HFS8 : fr / 8 <= alloc_ceiling / 8) by (apply Z.div_le_mono; clear - HFc HF4; lia).
assert (HAC8 : alloc_ceiling / 8 <= 17592184995840) by (apply Z.div_le_upper_bound; clear - C1; lia).
assert (HSHF : SHADOW_OFF + fr / 8 + 8 <= 17594332446728) by (clear - HFS8 HAC8 HSO; lia).
assert (HSPlo : alloc_ceiling + 16000 <= sp) by (clear - A1 Hslo0 Hceil0 HSTK; lia).
assert (HSPhi : sp + 160 <= spZ regs0) by (clear - A2; lia).
(* the registers at row 267 *)
assert (R2' : getr regs 2 = w64 sp) by (rewrite K2; unfold sp, spZ, w64; rewrite Z_to_bv_bv_unsigned; reflexivity).
assert (R9' : getr regs 9 = w64 sp) by (rewrite K9, R9; exact (eq_trans (eq_sym K2) R2')).
assert (R26' : getr regs 26 = w64 fr) by (rewrite K26; exact R26).
assert (R18' : getr regs 18 = w64 fr) by (rewrite K18; exact R18).
assert (R8' : getr regs 8 = w64 (spZ regs0)) by (rewrite K8; exact R8).
assert (R10' : getr regs 10 = w64 p') by (rewrite K10; exact R10).
assert (R19' : getr regs 19 = w64 v) by (rewrite K19; exact R19).
assert (R20' : getr regs 20 = w64 q) by (rewrite K20; exact R20).
assert (R23' : getr regs 23 = w64 SHADOW_OFF) by (rewrite K23; exact R23).
assert (R24' : getr regs 24 = w64 (SHADOW_OFF + fr / 8)) by (rewrite K24; exact R24).
assert (R27' : getr regs 27 = w64 (SHADOW_OFF + q / 8)) by (rewrite K27; exact R27).
assert (Rgp' : getr regs 3 = w64 (as_gp B)) by (rewrite K3, R3; exact Rgp0).
assert (Rtp' : getr regs 4 = w64 (as_tp B)) by (rewrite K4, R4; exact Rtp0).
(* the token *)
destruct (PjGrammar.skip (rest_atR tb text p)) as [|b y] eqn:Esk; [destruct HM as [Hc _]; discriminate Hc|].
destruct HM as (Harm & Hp'e & Hnth & Hws & R11).
(* the number arm's byte is no container opener (the free order's leaf form, VrdNum.vrd_frees_leaf) *)
assert (HB12 : b <> 123 /\ b <> 91)
  by (unfold vrd_arm_of in Harm; split; intros Hb; subst b; cbn in Harm; discriminate Harm).
assert (HR : rest_atR tb text p' = b :: y) by (first [exact HRest | rewrite HRest; exact Esk]).
assert (Htok' : vrd_num_tok (b :: y) = Some (txt, r)) by (rewrite <- HR; exact Htok).
destruct (vnt_tok _ _ _ Htok) as (Htxt & Hnum & Hn1).
set (n := Z.of_nat (length txt)).
assert (Hnr : n <= text + len - p').
{ assert (E1 : length (rest_atR tb text p') = (length txt + length r)%nat) by (rewrite Htxt, length_app; reflexivity).
  (unfold rest_atR in E1; rewrite length_skipn in E1; unfold n; lia). }
assert (Hn30 : n < 2 ^ 30).
{ (pose proof (vnt_maxrun tb (Z.to_nat (p' - text)) txt r Htxt Hnum); unfold n; lia). }
assert (Hgt : prhPv_gtrace d (rest_atR tb text p) = [EAlloc (Datatypes.S (length txt))]).
{ unfold prhPv_gtrace. rewrite (vnt_jv prh_jr_strtod d _ b y txt r [] Esk (eq_sym Harm) Htok').
  cbn [take]. destruct (whole prh_jr_strtod txt); reflexivity. }
destruct HROOM as (HRL & HMX & HLV). rewrite Hgt in HMX, HLV.
(unfold prh_maxreq in HMX; cbn in HMX).
(* the live room at the granted run's one event (the kit's cut: rd_room's live conjunct is PRH_Base.prh_live_evs, per event,
   PRH_FnParse.v blob f0d92dcec7e9 :248-251), at j = 0: the state's blocks_bytes (VrdNum.vrd_live_at0) plus the token
   block's request, which is fuzz_malloc's live premise at row 270 *)
assert (HLV0 : blocks_bytes S + (Z.of_nat (Datatypes.S (length txt)) + PresetReqAt.HEAD) <= LIVE_MAX).
{ pose proof (HLV 0%nat (PresetReqAt.HMal (Z.of_nat (Datatypes.S (length txt)) + PresetReqAt.HEAD)) eq_refl) as H0.
  rewrite vrd_live_at0 in H0. exact H0. }
clear HLV.
(* the row-270 call's live counts, from the text's position-free premises at S0 (vrd_disp_body's copy, HPK1 /
   HPK2) at the FIRST state of the granted events (PresetRun.pkR_prefix at 0): the call state is the frame take
   S = set_fs f S0, which moves no block, and sec_cnt / ccnt24 are PresetReqAt.cnt over the live requests by
   conversion (PRH_FnReader.v's header) *)
destruct HFS as (f & HSf).
assert (HSEC : YGcfRoomLive.sec_cnt S <= PresetLiveBounds.LSEC + PresetLiveBounds.DRV).
{ pose proof (PresetRun.pkR_prefix YGcfRoomLive.rl_sec_req
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) 0)
    as HP0.
  rewrite firstn_O, PresetReqAt.hlive_from_nil in HP0. rewrite HSf.
  change (YGcfRoomLive.sec_cnt (set_fs f S0))
    with (Z.of_nat (PresetReqAt.cnt YGcfRoomLive.rl_sec_req (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)))).
  clear - HP0 HPK1. lia. }
assert (HC24 : YGcfRoomLive.ccnt24 S <= PresetLiveBounds.L24 + PresetLiveBounds.DRV).
{ pose proof (PresetRun.pkR_prefix (PresetRoom.in_cls YG00.kBatchClass)
    (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p))) (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)) 0)
    as HP0.
  rewrite firstn_O, PresetReqAt.hlive_from_nil in HP0. rewrite HSf.
  change (YGcfRoomLive.ccnt24 (set_fs f S0))
    with (Z.of_nat (PresetReqAt.cnt (PresetRoom.in_cls YG00.kBatchClass) (PresetRoom.rs_live (YGcfRoom.room_of_cf S0)))).
  clear - HP0 HPK2. lia. }
(* the ledger at row 267: rows 157..266 wrote the frame's shadow and the stack slots only *)
assert (HLED267 : prh_ledger B ly S Hp W mem Lam peak cnt fail ran most own).
{ apply (vnt_ledger_keep ly S Hp W mem1 mem mem md Lam peak cnt fail ran most own
    (fun a => (SHADOW_OFF + fr / 8 <= a < SHADOW_OFF + fr / 8 + 8) \/ (sp <= a < sp + 32)) HAR HLED).
  - intros a Ha HX. apply HK; [exact Ha | intros H1; apply HX; left; exact H1 | intros H2; apply HX; right; exact H2].
  - (intros a [HX | HX] Hi; pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hl; unfold kLowMemEnd in Hl; lia).
  - intros a0 k0 i Hin Hi.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLED Hin) as (Hk0 & Hab & _).
    destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & Happ & _).
    assert (Hrq : 8 <= req_size (k0 + cf_head)) by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0); lia).
    unfold in_app in Happ.
    (intros [HX | HX]; clear - Hk0 H4096 Hc Happ Hrq HSHF HSPlo HSO HX Hi C1 C3 HKLS HW8 HF4; lia). }
(* the read-only view at row 267: no row since the dispatch wrote an image byte *)
assert (HROD267 : arodata_okP segs pa_relro_lo pa_relro_hi B (aview segs (w_H W) mem)).
{ intros a Hro Hno Her. pose proof (vrd_ro_img _ Hro) as Hi.
  pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hl. unfold kLowMemEnd in Hl.
  rewrite (HK a ltac:(lia) ltac:(lia) ltac:(lia)). exact (HROD a Hro Hno Her). }
assert (En : n = Z.of_nat (length txt)) by reflexivity.
(* lia unfolds a let-bound n in some atoms and not in others (measured: `req_size (n + 1 + cf_head)` failed);
   from here n is an opaque variable linked by En *)
clearbody n. rewrite <- En in R22.
(* the row-270 call's hull budget: the text's entry budget is for the granted trace, whose one event is that call's
   HMal (n + 1 + cf_head), and the fake-frame take S = set_fs f S0 keeps st_secs *)
assert (HHB : PresetHullBudget.hull_budget S [PresetReqAt.HMal (n + 1 + cf_head)]).
{ rewrite Hgt, (vnt_hevs_alloc (length txt) HI_head), <- En in HBUD. rewrite HSf.
  exact (PresetHullBudget.hull_budget_same S0 (set_fs f S0) _
    (YGcfSecsStep.secs_same_of_secs S0 (set_fs f S0) eq_refl) HBUD). }
(* bytes at and above the stack slots are the dispatch's *)
assert (KHI : forall a, sp + 32 <= a < 2 ^ 64 -> aview segs (w_H W) mem a = aview segs (w_H W) mem1 a).
{ intros a Ha. apply HK.
  - clear - Ha HSPlo C1 HP64. lia.
  - clear - Ha HSHF HSPlo C1 Hfr. rewrite <- Hfr. lia.
  - clear - Ha. lia. }
(* the node lives below alloc_ceiling *)
pose proof (vnt_node_home ly S Hp W mem md Lam peak cnt fail ran most own regs0 e v HAR HLED267 Hatv Hvw) as NODEH.
vnt_hidetac NODEH.
assert (NLO : v + 56 <= alloc_ceiling).
{ pose proof NODEH as NH. unfold vnt_hide in NH. destruct NH as [(bn & mn & Hbn & Hb1 & Hb2 & _) | (cidn & posn & Hfn & Hf1 & Hf2)].
  - destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hbn) as (_ & _ & Hc & _). clear - Hc Hb2; lia.
  - destruct (frames_bounds_x segs B ARx LAWS ly S Hp W mem md _ _ HAR Hfn) as (_ & Hc & _). clear - Hc Hf2; lia. }
(* the chain at the call (VrdPro.vrd_disp_chain) *)
(* the arithmetic the two applications below ask, each from the facts it needs only *)
(* src_rd's text bound is not strict at the kit's cut (its + 8 dropped); rd_pre's appended `text + len < alloc_ceiling`
   (vrd_disp_body's last conjunct) is *)
assert (N1 : 4096 <= p < alloc_ceiling) by (clear - Ht4 Hpr0 Htc HCEIL Hlen; lia).
assert (N2 : 0 <= p' < alloc_ceiling) by (clear - Hp'r Htc HCEIL Hlen Ht4; lia).
assert (N3 : alloc_ceiling + 16384 <= spZ regs0) by (clear - Hceil0 Hslo0 HSTK; lia).
assert (N4 : alloc_ceiling <= q) by (clear - N3 Hq0; lia).
assert (N5 : ly_top ly0 <= 2 ^ 64) by (clear - Htop20 H470 HP47 HP64; lia).
assert (N6 : spZ regs0 < ly_top ly0 - 16) by (clear - Hetop Etop Hq0 Hq1; lia).
assert (N7 : v + 56 <= spZ regs0) by (clear - NLO N3; lia).
assert (N8 : 2 ^ 46 <= sp <= 2 ^ 47 - 32) by (clear - HSPlo C1 HP46 HP47 HSPhi Hshi0 H470; lia).
assert (N9 : 0 <= fr /\ fr + 32 < 2 ^ 64) by (clear - HF4 HFc C1 HP64; lia).
assert (N10 : 0 <= n /\ p' + n < 2 ^ 62) by (clear - En Hp'r Ht4 Hnr Htl HP62; lia).
assert (N11 : spZ regs0 - STK_parse_value d <= sp /\ sp + 64 <= spZ regs0 + e /\ sp + 32 <= spZ regs0 - 16)
  by (clear - A1 HSTK HSPhi He0; lia).
assert (N12 : STK_fuzz_malloc + (spZ regs0 + e - sp) <= STK_parse_value d + e)
  by (clear - HSTKpv HSTKfm HPV A1; lia).
assert (N13 : n + 1 + cf_head < cf_malloc_max) by (clear - HMX En; lia).
assert (N14 : blocks_bytes S + (n + 1 + cf_head) <= LIVE_MAX) by (rewrite HI_head; clear - HLV0 En; lia).
assert (RQ0 : rdword (aview segs (w_H W0) mem0) q = Some p)
  by (apply vrd_rdword_of_val_mem; [exact Vq0 | clear - N1 C1 HP64; lia]).
assert (RQ : rdword (aview segs (w_H W) mem) q = Some p').
{ apply vrd_rdword_of_val_mem; [|clear - N2 C1 HP64; lia].
  apply (val_mem_kept segs (w_H W) (w_H W) mem1 mem q 8 p'); [|exact Vq].
  intros kk Hk. apply KHI. cbn in Hk. clear - Hk Hq0 HSPhi Hq1 HP64 Hetop Etop N5; lia. }
pose proof HSAV as (VS8 & VS16 & _).
assert (RS8 : rdword (aview segs (w_H W) mem) (spZ regs0 - 8) = Some (raZ regs0)).
{ apply vrd_rdword_of_val_mem; [|unfold raZ; apply bv_unsigned_in_range].
  apply (val_mem_kept segs (w_H W) (w_H W) mem1 mem _ 8 _); [|exact VS8].
  intros kk Hk. apply KHI. cbn in Hk. clear - Hk HSPhi N5 N6; lia. }
assert (RS16 : rdword (aview segs (w_H W) mem) (spZ regs0 - 16) = Some (s0Z regs0)).
{ apply vrd_rdword_of_val_mem; [|unfold s0Z; apply bv_unsigned_in_range].
  apply (val_mem_kept segs (w_H W) (w_H W) mem1 mem _ 8 _); [|exact VS16].
  intros kk Hk. apply KHI. cbn in Hk. clear - Hk HSPhi N5 N6; lia. }
assert (AGR : forall a, spZ regs0 <= a < 2 ^ 64 -> ~ inFP (rd_fp q v) a ->
          aview segs (w_H W) mem a = aview segs (w_H W0) mem0 a).
{ intros a Ha Hn. destruct (Z_lt_le_dec a (spZ regs0 + e)) as [Hw | Hw].
  - rewrite KHI by (clear - Ha HSPhi; lia). exact (HWIN a ltac:(clear - Ha Hw; lia) Hn).
  - apply F1; clear - Ha Hw N3; lia. }
assert (DEP : forall a, q + 16 <= a < q + 20 -> aview segs (w_H W) mem a = aview segs (w_H W0) mem0 a).
{ intros a Ha. rewrite KHI by (clear - Ha Hq0 HSPhi Hq1 Hetop Etop N5; lia).
  apply (vnt_vm_same _ _ _ _ (q + 16) 4 (Z.of_nat d)); [exact Vq16 | exact Vq160 | cbn; clear - Ha; lia]. }
assert (Hal8 : spZ regs0 mod 8 = 0).
{ clear - Hal0. apply Z.mod_divide in Hal0; [|lia]. destruct Hal0 as [a0 E0]. rewrite E0.
  replace (a0 * 16) with ((a0 * 2) * 8) by lia. apply Z.mod_mul. lia. }
assert (Hmod16 : (sp - (spZ regs0 + e)) mod 16 = 0).
{ clear - A3 Hal0 He16. apply Z.mod_divide in A3; [|lia]. apply Z.mod_divide in Hal0; [|lia].
  apply Z.mod_divide in He16; [|lia]. destruct A3 as [a3 E3]; destruct Hal0 as [a0 E0]; destruct He16 as [a1 E1].
  rewrite E3, E0, E1. replace (a3 * 32 - (a0 * 16 + a1 * 16)) with ((a3 * 2 - a0 - a1) * 16) by lia.
  apply Z.mod_mul. lia. }
destruct (vrd_disp_chain ly0 ly W0 W mem0 mem regs0 ch q v sp p p' HCH0 HCE RQ0 (proj1 N1) (proj2 N1) RQ
  (proj2 N2) N4 Hq8 Etop N5 ltac:(clear - N3; lia) ltac:(clear - HSPhi; lia) N6 Hal8 Hra4 RS8 RS16 AGR N7 DEP)
  as (ch1 & HCH1 & _).
(* rows 267..270 and the call *)
apply (vrd_seg_267_P B ARx SK LAWS PST_IMG P PLAW PCALL d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly S Hp k W regs
  mem md sp fr p' n ch1 Lam peak cnt fail ran most own _ HMAL HJ HPM R2' R9' R26' R8' R10' R22 Rgp' Rtp'
  N8 A3 (proj1 N9) (proj2 N9) (proj1 N2) (proj1 N10) (proj2 N10) V16 He0 (proj1 N11) (proj1 (proj2 N11))
  (proj2 (proj2 N11)) Hmod16 HSTKfm0 N12 HCH1 HROD267 HFZ HRL HUNIV HSEC HC24 HHB HLED267 N13 N14).
intros W2 ly2 S2 Hp2 regs2 mem2 md2 kk res HJ2 HPM2 HPR2 R10r HRL2 HHUL HT0 HT1 HOC HAP KP2 V16b V24b HCJ.
(* THE HULL USE from the entry state: fuzz_malloc's at its one event, which is the granted trace's, across the
   fake-frame take (st_secs kept); both exits state it *)
assert (HHU0 : PresetHullBudget.hull_used S0 S2 (PresetReqAt.rd_hevs (prhPv_gtrace d (rest_atR tb text p)))).
{ rewrite Hgt, (vnt_hevs_alloc (length txt) HI_head), <- En. rewrite HSf in HHUL.
  exact (PresetHullBudget.hull_used_app S0 (set_fs f S0) S2 [] _
    (PresetHullBudget.hull_used_secs S0 (set_fs f S0) [] eq_refl) HHUL). }
vnt_hidetac HAP.
destruct HCJ as (memc & mdc & kc & KC & HJc & HARc).
pose proof HJ2 as (HAR2 & Hly2 & _ & _ & _ & Hfrs2 & _ & _ & F1b & F2b & F3b & F4b & _ & Hpres2 & _ & _).
pose proof Hly2 as (_ & _ & _ & _ & _ & ELF02 & _ & _ & Etop02 & Eslo02 & Eshi02 & _).
pose proof HJc as (_ & Hlyc & _ & _ & _ & Hfrsc & _ & _ & G1 & G2 & G3 & G4 & _).
cbn [app] in Hfrsc.
pose proof Hlyc as (_ & _ & _ & _ & _ & ELF2 & _ & _ & Etop2 & Eslo2 & Eshi2 & _).
assert (EFA : forall cid pos', frame_addr ly2 cid pos' = frame_addr ly cid pos')
  by (intros cid pos'; unfold frame_addr; rewrite ELF2; reflexivity).
(* the registers at row 271: row 267's callee-saved ones *)
assert (Q2 : getr regs2 2 = w64 sp) by vnt_cs HPR2 2 R2'.
assert (Q9 : getr regs2 9 = w64 sp) by vnt_cs HPR2 9 R9'.
assert (Q19 : getr regs2 19 = w64 v) by vnt_cs HPR2 19 R19'.
assert (Q20 : getr regs2 20 = w64 q) by vnt_cs HPR2 20 R20'.
assert (Q23 : getr regs2 23 = w64 SHADOW_OFF) by vnt_cs HPR2 23 R23'.
assert (Q27 : getr regs2 27 = w64 (SHADOW_OFF + q / 8)) by vnt_cs HPR2 27 R27'.
assert (Q26 : getr regs2 26 = w64 fr) by vnt_cs HPR2 26 R26'.
assert (Q3 : getr regs2 3 = w64 (as_gp B)) by vnt_cs HPR2 3 Rgp'.
assert (Q4 : getr regs2 4 = w64 (as_tp B)) by vnt_cs HPR2 4 Rtp'.
(* the allocator's answer *)
assert (HRES : res = 0 \/ (cnt <> fail /\ 4096 + cf_head <= res /\ res mod 16 = 0 /\ ~ In res (map fst Lam) /\
  Hp2 = (res - cf_head) :: Hp /\ ablocks B ly2 S2 = ablocks B ly S ++ [(res - cf_head, n + 1 + cf_head)] /\
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF res (n + 1) /\
  (0 < n + 1 -> shadow_hull_vis (aview segs (w_H W2) mem2) res (n + 1)) /\
  prh_ledger B ly2 S2 Hp2 W2 mem2 ((res, n + 1) :: Lam) (Z.max peak (Ledger.lsum Lam + (n + 1)))
    ((cnt + 1) mod 2 ^ 64) fail ran most own)).
{ pose proof HAP as HAP'. unfold vnt_hide in HAP'.
  destruct HAP' as [(_ & Hr & _) | [(_ & Hr & _) | (C0 & Rr4 & Rr16 & RrL & HHr & HA & HRr & HHU & _ & HLD)]];
    [left; exact Hr | left; exact Hr |].
  right. exact (conj C0 (conj Rr4 (conj Rr16 (conj RrL (conj HHr (conj HA (conj HRr (conj HHU HLD)))))))). }
vnt_hidetac HRES.
assert (Hres64 : 0 <= res < 2 ^ 64).
{ pose proof HRES as HR'. unfold vnt_hide in HR'. destruct HR' as [-> | (_ & Rr4 & _ & _ & _ & HA & _)];
    [clear - HP64; lia|].
  destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 (res - cf_head) (n + 1 + cf_head) HAR2
    ltac:(rewrite HA; apply in_or_app; right; left; reflexivity)) as (_ & _ & Hc & _).
  assert (Hrq : n + 1 + cf_head <= req_size (n + 1 + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (n + 1 + cf_head) 0) as [E0|E0]; clear - N10 Hcf E0; lia).
  clear - Rr4 Hc Hrq C1 HP64 Hcf N10; lia. }
(* the blocks and the ledger after the call, as the generic after-call lemmas take them *)
assert (POST : exists D tr Lam2 peak2 cnt2 fail2 ran2,
  prh_ledger B ly2 S2 Hp2 W2 mem2 Lam2 peak2 cnt2 fail2 ran2 most own /\
  rd_blocks_move B ly S ly2 S2 D tr (rest_atR tb text p') d /\ Permutation Lam2 (D ++ Lam)).
{ pose proof HAP as HAP'. unfold vnt_hide in HAP'.
  destruct HAP' as [(_ & _ & _ & HA & HLD) | [(_ & _ & _ & HA & _ & _ & HLD) | (_ & _ & _ & _ & _ & HA & _ & _ & _ & HLD)]].
  - exists [], [], Lam, peak, ((cnt + 1) mod 2 ^ 64), SIZE_MAXZ, ran. split; [exact HLD|].
    split; [|apply Permutation_refl]. split; [intros a k0 []|].
    split; [rewrite HA; cbn [prhReader_ab map app]; apply Permutation_refl|].
    split; [rewrite Hfrsc; apply Permutation_refl|]. cbn [hpeakR]. clear; lia.
  - exists [], [], Lam. do 4 eexists. split; [exact HLD|].
    split; [|apply Permutation_refl]. split; [intros a k0 []|].
    split; [rewrite HA; cbn [prhReader_ab map app]; apply Permutation_refl|].
    split; [rewrite Hfrsc; apply Permutation_refl|]. cbn [hpeakR]. clear; lia.
  - exists [(res, n + 1)], [EAlloc (Datatypes.S (length txt))], ((res, n + 1) :: Lam),
      (Z.max peak (Ledger.lsum Lam + (n + 1))), ((cnt + 1) mod 2 ^ 64), fail, ran.
    split; [exact HLD|]. split; [|apply Permutation_refl].
    split; [intros a k0 [E | []]; injection E as <- <-;
            exact (vnt_fresh ly S ly2 S2 Hp2 W2 mem2 md2 res (n + 1) ltac:(clear - N10; lia) HAR2 HA)|].
    split; [rewrite HA; cbn [prhReader_ab map fst snd]; apply Permutation_app_comm|].
    split; [rewrite Hfrsc; apply Permutation_refl|].
    cbn [hpeakR PjGrammar.held_ev]. rewrite Htxt, length_app. clear - Hn1. lia. }
destruct POST as (D & tr & Lam2 & peak2 & cnt2 & fail2 & ran2 & HLED2 & HBM & HLp).
(* the ledger at the call state *)
assert (HLEDc : prh_ledger B ly S Hp W memc Lam peak cnt fail ran most own).
{ apply (vnt_ledger_keep ly S Hp W mem memc mem md Lam peak cnt fail ran most own (fun a => sp + 24 <= a < sp + 32)
    HAR HLED267).
  - intros a Ha Hx. exact (KC a Ha Hx).
  - intros a Hx Hi. pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hl. unfold kLowMemEnd in Hl.
    clear - Hx Hl HSPlo C1; lia.
  - intros a0 k0 i Hin Hi Hx.
    destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLED267 Hin) as (Hk0 & Hab & _).
    destruct (alx_blocks segs B ARx LAWS ly S Hp W mem md _ _ HAR Hab) as (_ & H4096 & Hc & _).
    assert (Hrq : 8 <= req_size (k0 + cf_head))
      by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0) as [E0|E0]; clear - Hk0 HW8 E0; lia).
    clear - Hc Hrq Hi Hx HSPlo; lia. }
(* shadow bytes the dispatch shows addressable are the call state's too: they miss the frame's eight
   (vnt_ra_off_frame), the stack slots and the slot rows 267..269 wrote *)
assert (FSH : forall i, 0 <= i < 8 -> aview segs (w_H W) mem1 (SHADOW_OFF + frame_addr ly 0 pos / 8 + i) =
          Some (nth (Z.to_nat i) vrd_frame_shadow 0)) by (destruct HFRAME as (_ & _ & _ & Hs); exact Hs).
assert (KSH : forall a n0, 0 <= a -> a + n0 <= 2 ^ 47 ->
          range_addressable (aview segs (w_H W) mem1) SHADOW_OFF a n0 ->
          range_addressable (aview segs (w_H W) memc) SHADOW_OFF a n0).
{ intros a n0 Ha0 Han Hra. apply (vnt_ra_keep (aview segs (w_H W) mem1)); [|exact Hra].
  intros x Hx. pose proof (vnt_ra_off_frame _ _ _ _ Hra FSH x Hx) as Hoff.
  assert (Hx8 : 0 <= x / 8 < 2 ^ 44).
  { split; [apply Z.div_pos; clear - Ha0 Hx; lia|]. apply Z.div_lt_upper_bound; [lia|]. clear - Hx Han HP47 HP44; lia. }
  unfold shadow_of_addr in *.
  rewrite (KC (SHADOW_OFF + x / 8) ltac:(clear - Hx8 HSO HP64 HP44; lia) ltac:(clear - Hx8 HSO HSPlo C1 HP44; lia)).
  apply HK; [clear - Hx8 HSO HP64 HP44; lia | exact Hoff | clear - Hx8 HSO HSPlo C1 HP44; lia]. }
(* the node's shadow after the call (IelemE's VrdIStep.vrd_node_ra_at, at the callee's journal) *)
assert (RAv56 : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF v 56).
{ apply (vrd_node_ra_at B ARx SK LAWS H_HL STK_fuzz_malloc sp [] ly S Hp W memc mdc Lam peak cnt fail ran most own
    regs0 e ly2 S2 Hp2 W2 mem2 md2 kc D tr (rest_atR tb text p') d Lam2 peak2 cnt2 fail2 ran2 most own v HARc HJc
    Hatv Hvw
    (KSH v 56 ltac:(clear - Hv4; lia) ltac:(clear - NLO C1 HP47; lia) Hrav) (fun x _ => inFP_nil _)
    HLEDc HBM HLED2 HLp). }
(* the text at the call state, then after the call (IelemE's VrdIStep.vrd_src_at) *)
assert (HSRCc : src_rd W memc text tb).
{ pose proof HSRC as (Hby & H4 & Hc8 & Ham & Hra & Hhu).
  assert (KT : forall x, text <= x < text + Z.of_nat (length tb) ->
            aview segs (w_H W) memc x = aview segs (w_H W) mem1 x).
  { intros x Hx. unfold amem_range in Ham.
    rewrite (KC x ltac:(clear - Hx H4 Hc8 C1 HP64; lia) ltac:(clear - Hx Hc8 HSPlo; lia)).
    apply HK; [clear - Hx H4 Hc8 C1 HP64; lia | rewrite <- Hfr; clear - Hx Ham HSHF C3 C5 HSO HF4; lia
              | clear - Hx Hc8 HSPlo; lia]. }
  split; [|split; [exact H4 | split; [exact Hc8 | split; [exact Ham | split]]]].
  - unfold bytes_at in *. apply (vrd_garr8_keep (w_H W) mem1 memc); [|exact Hby]. intros j Hj. apply KT. lia.
  - exact (KSH text (Z.of_nat (length tb)) ltac:(clear - H4; lia) ltac:(clear - Hc8 C1 HP47; lia) Hra).
  - intros Hn0 s0 Hs0. pose proof (Hhu Hn0 s0 Hs0) as Hv1.
    pose proof (vnt_hull_rng text (Z.of_nat (length tb)) s0 ltac:(clear - H4; lia) ltac:(clear - Hc8 C1 HP47; lia)
                  Hn0 Hs0) as Hs0r.
    rewrite (KC s0 ltac:(clear - Hs0r HSO HP44 HP64; lia) ltac:(clear - Hs0r HSO HP44 HSPlo C1; lia)).
    exact (aview_keeps_vis segs (w_H W) mem1 mem s0 (vrd_mg_of_pres _ _ _ HG) Hv1). }
assert (HSRC2 : src_rd W2 mem2 text tb).
{ apply (vrd_src_at B ARx SK LAWS H_HL H_zsal H_imgvis H_pst_ro STK_fuzz_malloc sp [] ly S Hp W memc mdc Lam peak cnt
    fail ran most own ly2 S2 Hp2 W2 mem2 md2 kc D tr (rest_atR tb text p') d Lam2 peak2 cnt2 fail2 ran2 most own
    text tb HJc
    ltac:(intros Hsk; destruct Hsk as (rr & Hr & _); destruct Hr) (fun a _ => inFP_nil a) HSRCc
    ltac:(rewrite Hlen; exact HHOME) HLEDc HBM HLED2 HLp). }
(* the cursor word and the cursor's shadow after the call: the real stack *)
assert (VQ2 : val_mem segs (rdW W2 mem2) q 8 p').
{ apply (val_mem_kept segs (w_H W) (w_H W2) mem1 mem2 q 8 p'); [|exact Vq].
  intros jj Hk. cbn in Hk.
  rewrite (KP2 (q + jj) ltac:(clear - Hk N4 Hq1 Hetop Etop Htop20 H470 HP47 HP64; lia)
             ltac:(clear - Hk Hq0 HSPhi; lia) ltac:(clear - Hk Hq0 HSPhi; lia)).
  apply KHI. clear - Hk Hq0 HSPhi Hq1 Hetop Etop Htop20 H470 HP47 HP64; lia. }
assert (RAq2 : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF q 8).
{ apply (vrd_stack_ra B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 q 8 HAR2).
  - rewrite Eslo02. clear - Hslo0 Hq0 HSTK; lia.
  - rewrite Eshi02. clear - Hq1 Hetop Etop Htop20; lia. }
assert (Amq8 : amem_range q 8) by (unfold amem_range; right; clear - N4 C1 C3 C4 Hq1 Hetop Etop Htop20 H470 HP47; lia).
assert (Amv24 : amem_range v 24) by (apply (vrd_amem_sub v 56); [exact Hamv | lia | lia | lia]).
assert (RAv24 : range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF v 24)
  by (apply (vrd_ra_sub _ _ v 56); [exact RAv56 | lia | lia]).
(* the node may be written: it is in a live block, or in a caller's live fake frame *)
assert (HWN : forall a, v <= a < v + 56 ->
          awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly2 S2) ly2
            [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly2 a).
{ intros a Ha. assert (HFPv : inFP (rd_fp q v) a)
    by (exists (v, v + 56); split; [cbn; tauto | cbn [fst snd]; clear - Ha; lia]).
  pose proof NODEH as NH. unfold vnt_hide in NH.
  destruct NH as [(bn & mn & Hbn & Hb1 & Hb2 & _) | (cidn & posn & Hfn & Hf1 & Hf2)].
  - left. right. left. split; [exact HFPv|]. exists bn, mn. split; [|clear - Ha Hb1 Hb2; lia].
    pose proof HRES as HR'. unfold vnt_hide in HR'.
    destruct HR' as [Hr0 | (_ & _ & _ & _ & _ & HA & _)]; [|rewrite HA; apply in_or_app; left; exact Hbn].
    pose proof HAP as HAP'. unfold vnt_hide in HAP'.
    destruct HAP' as [(_ & _ & _ & HA & _) | [(_ & _ & _ & HA & _) | (_ & Hr4 & _)]];
      [rewrite HA; exact Hbn | rewrite HA; exact Hbn | exfalso; clear - Hr0 Hr4 Hcf; lia].
  - rewrite HFr in Hfn. destruct Hfn as [E | Hfn].
    + exfalso. injection E as <- <-.
      pose proof (vrd_node_frame_disj W mem1 ly pos v HFRAME HF8 Hrav) as Hd.
      clear - Hd Hf1 Hf2 Hfb Ha; lia.
    + right. split; [exact HFPv|]. exists cidn, posn. split; [exact Hfn|].
      unfold frame_rng, in_zr. cbn [fst snd]. rewrite EFA. clear - Ha Hf1 Hf2; lia. }
assert (HWN16 : forall a, v + 16 <= a < v + 24 ->
          awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly2 S2) ly2
            [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly2 a) by (intros a Ha; apply HWN; clear - Ha; lia).
pose proof Hqv as Hqv'. unfold vnt_hide in Hqv'.
assert (N15 : v + 24 <= 2 ^ 47 - 2 ^ 23) by (assert (H23 : (2 : Z) ^ 23 = 8388608) by reflexivity;
  clear - NLO C1 HP47 H23; lia).
assert (N16 : 4096 <= q /\ q + 24 <= 2 ^ 47) by (clear - N4 C1 Hq1 Hetop Etop Htop20 H470 HP47; lia).
assert (N17 : 0 <= n < 2 ^ 32 /\ 0 <= p' < 2 ^ 64) by (clear - Hn30 En N2 C1 HP64; lia).
assert (N18 : (v + 24 <= sp - ESTACK \/ sp + 32 <= v + 16) /\ (q + 8 <= sp - ESTACK \/ sp + 32 <= q) /\
              (v + 24 <= q \/ q + 8 <= v + 16)) by (clear - NLO HSPlo HES Hq0 HSPhi Hqv'; lia).
assert (N19 : sp + 32 <= spZ regs0 + e /\ ESTACK + (spZ regs0 + e - sp) <= STK_parse_value d + e)
  by (clear - HSPhi He0 A1 HSTK HES; lia).
(* ---- facts both exits share: the node, this call's frame and the bytes above the stack slots across the call ---- *)
pose proof (vrd_node_frame_disj W mem1 ly pos v HFRAME HF8 Hrav) as FDJ. rewrite <- Hfr in FDJ.
assert (HinF2 : In (0, pos) (frames S2)) by (rewrite Hfrsc; exact HinF).
assert (EFL : flag_addr ly2 0 pos = flag_addr ly 0 pos) by (unfold flag_addr; rewrite ELF2; reflexivity).
assert (HABS : forall bn mn, In (bn, mn) (ablocks B ly S) -> In (bn, mn) (ablocks B ly2 S2)).
{ intros bn mn Hbn. pose proof HAP as HAP'. unfold vnt_hide in HAP'.
  destruct HAP' as [(_ & _ & _ & HA & _) | [(_ & _ & _ & HA & _) | (_ & _ & _ & _ & _ & HA & _)]];
    rewrite HA; [exact Hbn | exact Hbn | apply in_or_app; left; exact Hbn]. }
assert (NIMG : forall a, v <= a < v + 56 -> ~ in_img segs a).
{ intros a Ha. pose proof NODEH as NH. unfold vnt_hide in NH.
  destruct NH as [(bn & mn & Hbn & Hb1 & Hb2 & _) | (cidn & posn & Hfn & Hf1 & Hf2)].
  - exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ bn mn a HAR Hbn ltac:(clear - Ha Hb1 Hb2; lia)).
  - exact (frm_img_x segs B ARx LAWS _ _ _ _ _ _ cidn posn a HAR Hfn ltac:(clear - Ha Hf1 Hf2; lia)). }
assert (HBAND : fst (ly_img ly) <= 0x10000 /\ 0x600000 <= fst (ly_img ly) + snd (ly_img ly)).
{ apply (img_band_x segs B ARx LAWS ly S Hp W mem md 0x10000 0x600000 HAR).
  - exact (proj1 vnt_img_wit).
  - exact (proj2 vnt_img_wit). }
assert (NBAND : v + 56 <= 0x10000 \/ 0x600000 <= v).
{ pose proof NODEH as NH. unfold vnt_hide in NH.
  destruct NH as [(bn & mn & Hbn & Hb1 & Hb2 & _) | (cidn & posn & Hfn & Hf1 & Hf2)].
  - destruct (blk_off_band_x segs B ARx LAWS ly S Hp W mem md 0x10000 0x600000 bn mn HAR (proj1 HBAND) (proj2 HBAND)
      ltac:(reflexivity) Hbn) as [Hl | Hl]; [left; clear - Hl Hb1 Hb2; lia | right; clear - Hl Hb1; lia].
  - pose proof (frm_above_band_x segs B ARx LAWS ly S Hp W mem md 0x600000 cidn posn HAR (proj2 HBAND) Hfn) as Hh.
    right. clear - Hh Hf1; lia. }
assert (FBAND : 0x600000 <= fr)
  by exact (frm_above_band_x segs B ARx LAWS ly S Hp W mem md 0x600000 0 pos HAR (proj2 HBAND) HinF).
assert (KN2 : forall a, v <= a < v + 56 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem1 a).
{ intros a Ha.
  assert (E1 : aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a).
  { pose proof NODEH as NH. unfold vnt_hide in NH.
    destruct NH as [(bn & mn & Hbn & Hb1 & Hb2 & _) | (cidn & posn & Hfn & Hf1 & Hf2)].
    - replace a with (bn + (a - bn)) by ring.
      exact (G2 bn mn (a - bn) Hbn (HABS bn mn Hbn) ltac:(clear - Ha Hb1 Hb2; lia) (inFP_nil _)).
    - exact (G4 cidn posn a Hfn ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; clear - Ha Hf1 Hf2; lia)
               (inFP_nil _)). }
  rewrite E1, (KC a ltac:(clear - Ha NLO C1 HP64 Hv4; lia) ltac:(clear - Ha NLO HSPlo; lia)).
  unfold amem_range in Hamv.
  apply HK; [clear - Ha NLO C1 HP64 Hv4; lia | rewrite <- Hfr; clear - Ha Hamv HSHF C3 C5 HSO HF4; lia
            | clear - Ha NLO HSPlo; lia]. }
assert (KF2 : forall a, fr <= a < fr + 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem1 a).
{ intros a Ha.
  rewrite (G4 0 pos a HinF ltac:(left; unfold in_zr, frame_rng; cbn [fst snd]; rewrite Hfb, <- Hfr; clear - Ha; lia)
             (inFP_nil _)).
  rewrite (KC a ltac:(clear - Ha HF4 HFc C1 HP64; lia) ltac:(clear - Ha HFc HSPlo; lia)).
  unfold in_app in HFapp.
  apply HK; [clear - Ha HF4 HFc C1 HP64; lia | rewrite <- Hfr; clear - Ha HFapp HSHF C3 HSO HF4 HKLS; lia
            | clear - Ha HFc HSPlo; lia]. }
assert (KH2 : forall a, sp + 32 <= a < 2 ^ 64 -> aview segs (w_H W2) mem2 a = aview segs (w_H W) mem1 a).
{ intros a Ha. rewrite (KP2 a ltac:(clear - Ha HSPlo; lia) ltac:(clear - Ha; lia) ltac:(clear - Ha; lia)).
  exact (KHI a Ha). }
assert (NZ1 : forall a, v <= a < v + 56 -> aview segs (w_H W) mem1 a = Some 0).
{ intros a Ha. unfold pj_zeroR in Hzv.
  destruct (Hzv (Z.to_nat (a - v)) ltac:(rewrite repeat_length; clear - Ha; lia)) as [Hz1 _].
  rewrite nth_repeat in Hz1.
  exact (vnt_zero_bytes _ _ _ 1 a Hz1 ltac:(change (Z.of_nat 1) with 1; clear - Ha; lia)). }
assert (NZ2 : forall a, v <= a < v + 56 -> aview segs (w_H W2) mem2 a = Some 0)
  by (intros a Ha; rewrite (KN2 a Ha); exact (NZ1 a Ha)).
assert (QB : forall a, q <= a < q + 24 -> sp + 32 <= a < 2 ^ 64)
  by (intros a Ha; clear - Ha Hq0 HSPhi Hq1 Hetop Etop Htop20 H470 HP47 HP64; lia).
assert (QIMG : forall x, q <= x < q + 24 -> 0 <= x < 2 ^ 64 /\ ~ in_img segs x).
{ intros x Hx. pose proof (QB x Hx) as Hb. split; [clear - Hb N8 HP46; lia|].
  intros Hi. pose proof (@pa_segs_low _ _ PI_prog_A x Hi) as Hl. unfold kLowMemEnd in Hl. clear - Hb Hl HSPlo C1; lia. }
assert (WB : forall a, spZ regs0 <= a < spZ regs0 + e -> sp + 32 <= a < 2 ^ 64)
  by (intros a Ha; clear - Ha HSPhi Hetop Etop Htop20 H470 HP47 HP64; lia).
pose proof (vnt_ledger_bounds _ _ _ _ _ _ _ _ _ _ _ _ HLED) as (HLP & HPK0 & HC0 & _).
assert (HCN : cnt + 1 < 2 ^ 64) by (clear - Hcnt HC0; lia).
destruct (Z.eq_dec res 0) as [Hres0 | Hres0].
{ (* ==== THE NULL BLOCK: rows 271..277 to row 326, then the refusal join (rows 326..328) ==== *)
  apply (vrd_seg_271_P B ARx SK LAWS H_checked_memcpy_xm P PLAW PCALL d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly2 S2
    Hp2 (k + kk) W2 regs2 mem2 md2 sp fr p' n res _ HJ2 HPM2 Q2 Q9 Q19 Q20 Q23 Q27 Q26 R10r Q3 Q4 N8 A3 (proj1 N9) (proj2 N9) Hv4 N15
    (proj1 N16) (proj2 N16) Hres64 (proj1 N17) (proj2 N17) (proj1 N18) (proj1 (proj2 N18)) (proj2 (proj2 N18))
    He0 (proj1 N11) (proj1 N19) Hmod16 (proj2 N19) V16b V24b VQ2 HWN16 RAv24 Amv24 RAq2 Amq8
    (fun Hn0 => False_ind _ (Hn0 Hres0))).
  2: { intros regs4 mem4 md4 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hr0. exfalso. exact (Hr0 Hres0). }
  intros regs3 mem3 md3 HJ3 HPM3 TK3 R25c KP3 MG3 V16z _.
  pose proof (vnt_regs1 regs3 regs2 regs TK3 HPR2) as L3.
  (* the node is unchanged: rows 271..277 stored 0 in its str word, which held 0 *)
  assert (K32 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp + 8 <= a < sp + 16) ->
            aview segs (w_H W2) mem3 a = aview segs (w_H W2) mem2 a).
  { intros a Ha Hs. destruct (Z_lt_le_dec a (v + 16)) as [Hl | Hl]; [|destruct (Z_lt_le_dec a (v + 24)) as [Hm | Hm]].
    - exact (KP3 a Ha ltac:(clear - Hl; lia) Hs).
    - rewrite (vnt_zero_bytes _ _ _ 8 a V16z ltac:(change (Z.of_nat 8) with 8; clear - Hl Hm; lia)).
      symmetry. exact (NZ2 a ltac:(clear - Hl Hm; lia)).
    - exact (KP3 a Ha ltac:(clear - Hm; lia) Hs). }
  assert (KN3 : forall a, v <= a < v + 56 -> aview segs (w_H W2) mem3 a = aview segs (w_H W) mem1 a).
  { intros a Ha. rewrite (K32 a ltac:(clear - Ha Hv4 NLO C1 HP64; lia) ltac:(clear - Ha NLO HSPlo; lia)).
    exact (KN2 a Ha). }
  assert (KQ3 : forall a, sp + 32 <= a < 2 ^ 64 -> aview segs (w_H W2) mem3 a = aview segs (w_H W) mem1 a).
  { intros a Ha. rewrite (K32 a ltac:(clear - Ha N8 HP46; lia) ltac:(clear - Ha; lia)). exact (KH2 a Ha). }
  assert (KF3 : forall a, fr <= a < fr + 64 -> aview segs (w_H W2) mem3 a = aview segs (w_H W) mem1 a).
  { intros a Ha. rewrite (K32 a ltac:(clear - Ha HF4 HFc C1 HP64; lia) ltac:(clear - Ha HFc HSPlo; lia)).
    exact (KF2 a Ha). }
  (* the ledger after the refusal, at the current memory *)
  assert (LED3 : forall Lx px cx fx' rx, prh_ledger B ly2 S2 Hp2 W2 mem2 Lx px cx fx' rx most own ->
            prh_ledger B ly2 S2 Hp2 W2 mem3 Lx px cx fx' rx most own).
  { intros Lx px cx fx' rx HLD.
    apply (vnt_ledger_keep_pst ly2 S2 Hp2 W2 mem2 mem3 mem2 md2 Lx px cx fx' rx most own
      (fun a => sp + 8 <= a < sp + 16) HAR2 HLD).
    - exact K32.
    - intros a Ha Hx. pose proof (PST_IMG a Ha) as Hi. pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hl.
      unfold kLowMemEnd in Hl. clear - Hx Hl HSPlo C1; lia.
    - intros a0 k0 i Hin Hi Hx. destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLD Hin) as (Hk0 & Hab & _).
      destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab) as (_ & H4096 & Hc & _).
      assert (Hrq : 8 <= req_size (k0 + cf_head))
        by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0) as [E0|E0]; clear - Hk0 HW8 E0; lia).
      clear - Hc Hrq Hi Hx HSPlo; lia. }
  (* the refusal's model: the token present, the oracle's first answer false (at the text's strtod name) *)
  assert (HJV0 : jr_value ReaderRes.jr_strtod d (rest_atR tb text p) [false] =
                 (None, [EFail (Datatypes.S (length txt))], [])).
  { rewrite (vnt_jv ReaderRes.jr_strtod d _ b y txt r [false] Esk (eq_sym Harm) Htok'). reflexivity. }
  (* fuzz_malloc's NULL-arm transfer and outcome clause at the frame-taken call state S = set_fs f S0 *)
  rewrite HSf in HT0, HOC. rewrite En in HOC.
  assert (HCOM : forall peak' fail' ran',
            rd_ledger_move Lam peak cnt fail ran most [false] [EAlloc (Datatypes.S (length txt))]
              [EFail (Datatypes.S (length txt))] [] Lam peak' ((cnt + 1) mod 2 ^ 64) fail' ran' ->
            prh_ledger B ly2 S2 Hp2 W2 mem2 Lam peak' ((cnt + 1) mod 2 ^ 64) fail' ran' most own ->
            ablocks B ly2 S2 = ablocks B ly S ->
            vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos (-1) ly2 S2 Hp2 W2 mem3).
  { intros peak' fail' ran' HLM HLD HA. unfold vrd_pv_post.
    exists [false], None, [EFail (Datatypes.S (length txt))], [], [], Lam, peak', ((cnt + 1) mod 2 ^ 64), fail', ran'.
    split; [exact HJV0|].
    split; [exact (LED3 _ _ _ _ _ HLD)|].
    split; [exact HRL2|].
    split; [exact HHU0|].
    (* the live set: the NULL moves no block, and rd_hevs [EFail _] = [] *)
    split.
    { rewrite <- (vnt_live_ab ly2 S2), HA, HSf.
      change (map snd (ablocks B ly (set_fs f S0))) with (map snd (ablocks B ly S0)). rewrite (vnt_live_ab ly S0).
      exact (Permutation_refl _). }
    (* THE POSITION TRANSFER at E = []: fuzz_malloc's res = 0 transfer *)
    split; [exact (vnt_transfer_null S0 f S2 (Datatypes.S (length txt)) (HT0 Hres0))|].
    (* THE OUTCOME: its premises put a consumer HMal with cnt <> fail at the call, where fuzz_malloc grants *)
    split.
    { rewrite Hgt. intros sm x os i H0 hist HPo HRo HCo HFo. exfalso.
      exact (vnt_outcome_null False S0 f S2 res (length txt) cnt fail HI_head Hres0 HOC sm x os i H0 hist HPo HRo HCo
        HFo). }
    (* THE OUTCOME OF AN INJECTED READING: the one call is the granted trace's one allocation, so the guard's window
       puts the chosen failure at it (fail = cnt), and its failed outcome is the chosen one *)
    split; [rewrite Hgt; intros sm x os i H0 hist _ _ _ Hw ii Hii _; cbn in Hii, Hw; lia|].
    split; [rewrite Hgt; exact HLM|].
    split; [intros a0 k0 []|].
    split; [rewrite HA; cbn [prhReader_ab map app]; rewrite HAB; apply Permutation_refl|].
    split; [rewrite Hfrsc, HFr; apply Permutation_refl|].
    split; [cbn [hpeakR PjGrammar.held_ev]; clear; lia|].
    split; [rewrite (YCbq.blocks_bytes_bsum B ly2 S2), (YCbq.blocks_bytes_bsum B ly0 S0), HA, <- HAB;
            unfold prh_held; cbn [PjGrammar.held PjGrammar.held_ev PjGrammar.calls PjGrammar.is_call];
            clear - Hcf; lia|].
    split; [reflexivity|].
    split; [reflexivity|].
    (* THE FREE ORDER (the kit's cut, FREEORD-NONE): the NULL leaves the node zeroed, no block (VrdNum.vrd_zero_fo);
       the model's list is the leaf's of [EFail _], none *)
    split.
    { intros _ nn _. exists []. split.
      - apply vrd_zero_fo.
        + split; [exact Hv8|].
          apply (vnt_rw_xfer (w_H W) (w_H W2) mem1 mem3 v 56); [| exact KN3 | exact (proj2 Hrwv)].
          intros x Hx. split; [clear - Hx Hv4 NLO C1 HP64; lia | exact (NIMG x Hx)].
        + unfold pj_zeroR in Hzv |- *. apply (vnt_garr8_xfer (w_H W) (w_H W2) mem1 mem3 v); [|exact Hzv].
          intros x Hx. rewrite repeat_length in Hx. change (Z.of_nat 56) with 56 in Hx. exact (KN3 x Hx).
      - cbn [map]. rewrite (vrd_frees_leaf d (rest_atR tb text p) [false] b y Esk (proj1 HB12) (proj2 HB12)), HJV0.
        reflexivity. }
    split.
    { exists p', (Z.of_nat d). split; [clear - Hp'r; lia|]. split; [clear - Hd32; lia|].
      split; [apply (vnt_vm_move (w_H W) (w_H W2) mem1 mem3 q q 8 p'); [|exact Vq];
              intros jj Hk; apply KQ3; apply QB; clear - Hk; lia|].
      split; [apply (vnt_vm_move (w_H W) (w_H W2) mem1 mem3 (q + 8) (q + 8) 8 _); [|exact Vq8];
              intros jj Hk; apply KQ3; apply QB; clear - Hk; lia|].
      split; [apply (vnt_vm_move (w_H W) (w_H W2) mem1 mem3 (q + 16) (q + 16) 4 _); [|exact Vq16];
              intros jj Hk; apply KQ3; apply QB; clear - Hk; lia|].
      apply (vnt_rw_xfer (w_H W) (w_H W2) mem1 mem3 q 24); [exact QIMG | | exact Hrwq].
      intros x Hx. apply KQ3. exact (QB x Hx). }
    apply vrd_zero_fd.
    - split; [exact Hv8|].
      apply (vnt_rw_xfer (w_H W) (w_H W2) mem1 mem3 v 56); [| exact KN3 | exact (proj2 Hrwv)].
      intros x Hx. split; [clear - Hx Hv4 NLO C1 HP64; lia | exact (NIMG x Hx)].
    - unfold pj_zeroR in Hzv |- *. apply (vnt_garr8_xfer (w_H W) (w_H W2) mem1 mem3 v); [|exact Hzv].
      intros x Hx. rewrite repeat_length in Hx. change (Z.of_nat 56) with 56 in Hx. exact (KN3 x Hx). }
  assert (HPVP : vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos (-1) ly2 S2 Hp2 W2 mem3).
  { pose proof HAP as HAP'. unfold vnt_hide in HAP'.
    destruct HAP' as [(Hc0 & _ & _ & HA & HLD) | [(Hc0 & _ & _ & HA & _ & _ & HLD) | (_ & Rr4 & _)]].
    - (* the chosen failure: g_fail_at := SIZE_MAX, g_ran_out and g_peak untouched *)
      apply (HCOM peak SIZE_MAXZ ran); [|exact HLD|exact HA].
      pose proof (vle_fail_chosen Lam peak cnt fail ran most [EAlloc (Datatypes.S (length txt))]
        (Datatypes.S (length txt)) HC0 HCN Hc0 HLP HPK0) as HLM.
      replace (cnt + 1) with ((cnt + 1) mod 2 ^ 64) in HLM by (apply Z.mod_small; clear - HC0 HCN; lia). exact HLM.
    - (* the refusal (#102): g_peak takes live + n, g_ran_out is set only when n <= g_most; the granted trace's
         first held amount is the token block's n = |txt| + 1 *)
      rewrite En in HLD.
      pose proof (vle_fail_refused Lam peak cnt fail ran most [EAlloc (Datatypes.S (length txt))]
        (Datatypes.S (length txt)) (Z.of_nat (Datatypes.S (length txt))) HC0 HCN Hc0 HLP HPK0
        ltac:(cbn; reflexivity)) as HLM.
      replace (cnt + 1) with ((cnt + 1) mod 2 ^ 64) in HLM by (apply Z.mod_small; clear - HC0 HCN; lia).
      replace (Z.of_nat (Datatypes.S (length txt))) with (Z.of_nat (length txt) + 1) in HLM by lia.
      exact (HCOM _ _ _ HLM HLD HA).
    - exfalso. clear - Hres0 Rr4 Hcf; lia. }
  assert (HREF : vrd_ref_a B ARx SK d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos (-1)
                   (vrd_pv_post B d e q v text len p tb ly0 S0 Lam peak cnt fail ran most own pos (-1)) W2
                   (cfg_at segs (BASE + vrd_row 326) regs3 mem3 md3)).
  { exists regs3, mem3, md3, ly2, S2, Hp2, (k + kk).
    split; [rewrite <- vrd_pc_ref; reflexivity|].
    split; [exact HJ3|].
    split; [intros a Ha Hn; rewrite (KQ3 a (WB a Ha)); exact (HWIN a Ha Hn)|].
    split; [vnt_rg L3 8 R8'|].
    split; [rewrite EFA, <- Hfr; vnt_rg L3 18 R18'|].
    split; [rewrite EFA, <- Hfr; vnt_rg L3 26 R26'|].
    split; [rewrite EFA, <- Hfr; vnt_rg L3 24 R24'|].
    split; [vnt_rg L3 21 R21|].
    split; [vnt_rg L3 3 (eq_trans Rgp' (eq_sym Rgp0))|].
    split; [vnt_rg L3 4 (eq_trans Rtp' (eq_sym Rtp0))|].
    split; [exact Hret|].
    split.
    { pose proof HSAV as HS'. unfold vrd_saved in HS' |- *.
      destruct HS' as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
      repeat split; (eapply val_mem_kept; [|eassumption]); intros jj Hk; cbn in Hk; apply KQ3;
        clear - Hk HSPhi Hshi0 H470 HP47 HP64; lia. }
    split.
    { rewrite EFA, EFL. destruct HFRAME as (_ & _ & VF56 & _).
      apply (val_mem_kept segs (w_H W) (w_H W2) mem1 mem3 (frame_addr ly 0 pos + 56) 8 _); [|exact VF56].
      intros jj Hk. cbn in Hk. apply KF3. rewrite <- Hfr. clear - Hk; lia. }
    split; [exact HinF2|]. split; [exact HFZ|]. split; [exact He0|].
    exact HPVP. }
  eapply SRr_mono.
  - refine (vrd_ref_join_P B ARx SK LAWS P PLAW d CW e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos (-1) _ W2 _ _ HREF HPM3).
    apply (vrd_pv_post_sh_frame B ARx LAWS);
      [exact PST_IMG | clear - N4 C1 C2; lia | clear - Hq1 Hetop Etop Htop20 H470 HP47 HP64; lia | clear - Hv4; lia
      | exact Hamv | rewrite <- Hlen; exact Hamt].
  - intros W' c' _ (H & HP'). split; [exists fx, pos, (-1); exact H | exact HP']. }
(* ==== THE BLOCK: rows 271..283 and the copy, rows 284..298 and strtod, then rows 299..328 (WalkNumEnd) ==== *)
pose proof HRES as HR'. unfold vnt_hide in HR'.
destruct HR' as [Hr | (Cnf & Rr4 & Rr16 & RrL & HHr & HA & HRA & HHU & HLDs)]; [exfalso; exact (Hres0 Hr)|].
pose proof (vnt_fresh ly S ly2 S2 Hp2 W2 mem2 md2 res (n + 1) ltac:(clear - N10; lia) HAR2 HA) as Hfresh.
assert (Hin2 : In (res - cf_head, n + 1 + cf_head) (ablocks B ly2 S2))
  by (rewrite HA; apply in_or_app; right; left; reflexivity).
destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hin2) as (_ & _ & Hc & Happ & _).
assert (Hrq : n + 1 + cf_head <= req_size (n + 1 + cf_head))
  by (unfold req_size; destruct (Z.eqb_spec (n + 1 + cf_head) 0) as [E0|E0]; clear - N10 Hcf E0; lia).
(* stated apart: a `ltac:(lia)` inside an application argument failed on this goal twice (measured) *)
assert (Hrq0 : 0 < req_size (n + 1 + cf_head)) by (clear - Hrq N10 Hcf; lia).
assert (Hlen0 : 0 < len) by (clear - Hp'r Hp'e; lia).
(* the node and the text are apart from the new block *)
assert (NB : forall x, v <= x < v + 56 -> ~ (res - cf_head <= x < res - cf_head + req_size (n + 1 + cf_head))).
{ intros x Hx Hxb. pose proof NODEH as NH. unfold vnt_hide in NH.
  destruct NH as [(bn & mn & Hbn & Hb1 & Hb2 & _) | (cidn & posn & Hfn & Hf1 & Hf2)].
  - assert (Hne : (bn, mn) <> (res - cf_head, n + 1 + cf_head)) by (intros E; apply Hfresh; rewrite <- E; exact Hbn).
    pose proof (sep_blocks_x segs B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR2
                  ltac:(rewrite HA; apply in_or_app; left; exact Hbn) Hin2 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hx Hxb Hb1 Hb2; lia.
  - assert (Hfn2 : In (cidn, posn) (frames S2)) by (rewrite Hfrsc; exact Hfn).
    pose proof (sep_block_frame_x segs B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR2 Hin2 Hfn2) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA in Hd. clear - Hd Hx Hxb Hf1 Hf2; lia. }
assert (TB : forall x, text <= x < text + len -> ~ (res - cf_head <= x < res - cf_head + req_size (n + 1 + cf_head))).
{ intros x Hx Hxb.
  destruct (vnt_text_where ly S Hp W mem Lam peak cnt fail ran most own text len x HLED267 HHOME Hx)
    as [(bt & mt & Hbt & Hxt) | Hi].
  - assert (Hne : (bt, mt) <> (res - cf_head, n + 1 + cf_head)) by (intros E; apply Hfresh; rewrite <- E; exact Hbt).
    pose proof (sep_blocks_x segs B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR2
                  ltac:(rewrite HA; apply in_or_app; left; exact Hbt) Hin2 Hne) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hxt Hxb; lia.
  - exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ _ _ x HAR2 Hin2 Hxb Hi). }
pose proof (vnt_interval v 56 (res - cf_head) (req_size (n + 1 + cf_head)) ltac:(reflexivity) Hrq0 NB) as NBi.
pose proof (vnt_interval text len (res - cf_head) (req_size (n + 1 + cf_head)) Hlen0 Hrq0 TB) as TBi.
pose proof HSRC2 as (Hby2 & H42 & Hc82 & Ham2 & Hra2 & Hhu2). rewrite Hlen in Hc82, Ham2, Hra2, Hhu2.
pose proof Htv as Htv'. unfold vnt_hide in Htv'. specialize (Htv' Hlen0).
(* the memcpy's premises: the allocator's success arm, the token in the text *)
assert (HCPY : res <> 0 ->
  res + n + 1 <= alloc_ceiling /\
  (forall a, res <= a < res + n + 1 -> in_tmp_block (ablocks B ly0 S0) (ablocks B ly2 S2) a) /\
  amem_range res (n + 1) /\ range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF res (n + 1) /\
  (0 < n -> shadow_hull_vis (aview segs (w_H W2) mem2) res n) /\
  (v + 24 <= res \/ res + n + 1 <= v + 16) /\
  p' + n <= alloc_ceiling /\ (p' + n <= v + 16 \/ v + 24 <= p') /\ (res + n <= p' \/ p' + n <= res) /\
  (forall a, p' <= a < p' + n -> aview segs (w_H W2) mem2 a <> None) /\ amem_range p' n /\
  range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF p' n /\
  (0 < n -> shadow_hull_vis (aview segs (w_H W2) mem2) p' n)).
{ intros _.
  split; [clear - Hc Hrq Hcf; lia|].
  split; [intros a Ha; exists (res - cf_head), (n + 1 + cf_head); split; [exact Hin2|];
          split; [rewrite <- HAB; exact Hfresh | clear - Ha Hrq Hcf; lia]|].
  split; [unfold in_app in Happ; unfold amem_range;
          unfold ASAN_CEIL in Happ;
          clear - Happ Hrq Hcf C1 C3 C4 C5 HKLS; lia|].
  split; [exact HRA|].
  split; [intros Hn0; apply (vrd_hull_sub _ res (n + 1) res n); [apply HHU; clear - Hn0; lia | clear; lia | clear; lia | exact Hn0]|].
  split; [clear - NBi Hrq Hcf; lia|].
  split; [clear - Hc82 Hp'r Hnr; lia|].
  split; [clear - Htv' Hp'r Hnr; lia|].
  split; [clear - TBi Hrq Hcf Hp'r Hnr; lia|].
  split; [intros a Ha; destruct (Hby2 (Z.to_nat (a - text)) ltac:(clear - Ha Hp'r Hnr Hlen; lia)) as [Hv _];
          apply (vnt_vm_some (w_H W2) mem2 _ 1 _ a Hv); clear - Ha Hp'r Hnr; lia|].
  split; [apply (vrd_amem_sub text len); [exact Ham2 | clear - Hp'r Hnr N10; lia | clear - Hp'r Hnr N10; lia | clear - Hp'r Hnr N10; lia]|].
  split; [apply (vrd_ra_sub _ _ text len); [exact Hra2 | clear - Hp'r Hnr N10; lia | clear - Hp'r Hnr N10; lia]|].
  intros Hn0. apply (vrd_hull_sub _ text len p' n); [apply Hhu2; clear - Hlen0; lia | clear - Hp'r Hnr N10; lia | clear - Hp'r Hnr N10; lia | exact Hn0]. }
pose proof (HCPY Hres0) as (HC1 & HC2 & HC3 & HC4 & HC5 & HC6 & _).
assert (SBF : res - cf_head + req_size (n + 1 + cf_head) <= fr \/ fr + 64 <= res - cf_head).
{ pose proof (sep_block_frame_x segs B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR2 Hin2 HinF2) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA, Hfb, <- Hfr in Hd. exact Hd. }
assert (HBAND2 : fst (ly_img ly2) <= 0x10000 /\ 0x600000 <= fst (ly_img ly2) + snd (ly_img ly2)).
{ apply (img_band_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 0x10000 0x600000 HAR2).
  - exact (proj1 vnt_img_wit).
  - exact (proj2 vnt_img_wit). }
assert (BBAND : forall b0 m0, In (b0, m0) (ablocks B ly2 S2) -> b0 + req_size m0 <= 0x10000 \/ 0x600000 <= b0).
{ intros b0 m0 Hb0. exact (blk_off_band_x segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 0x10000 0x600000 b0 m0 HAR2
                             (proj1 HBAND2) (proj2 HBAND2) ltac:(reflexivity) Hb0). }
assert (N20 : STK_RT_STRTOD + (spZ regs0 + e - sp) <= STK_parse_value d + e) by (clear - HSTKpv HSTKst HPV A1; lia).
assert (HSPS : alloc_ceiling <= sp - STK_RT_STRTOD) by (clear - N20 Hslo0 Hceil0; lia).
assert (HGG : si_got_guard strtod_img_A = 666776) by reflexivity.
assert (HGT : si_globals_top strtod_img_A = 6291456) by reflexivity.
assert (HIL : si_img_lo strtod_img_A = 65536) by reflexivity.
(* the GOT guard at row 271: read-only image cells (in_img), whose view is the ROM's by AR_laws_x's const-cell law at
   the state after the call (the guard is one of B's const cells, B_got_const) and the ROM bytes of the word
   (strtod_row.strtod_got_A); the route of S8aNumC.v's HGOT *)
assert (GOT2 : forall a, 666776 <= a < 666784 ->
          in_img segs a /\
          aview segs (w_H W2) mem2 a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))).
{ intros a Ha.
  assert (Hro : in_roP segs pa_relro_lo pa_relro_hi a).
  { right. change (A_prog_relro_lo <= a < A_prog_relro_hi). unfold A_prog_relro_lo, A_prog_relro_hi. clear - Ha; lia. }
  split; [exact (vrd_ro_img _ Hro)|].
  pose proof (alx_const_cells segs B ARx LAWS _ _ _ _ _ _ HAR2) as HGC.
  rewrite Forall_forall in HGC. specialize (HGC _ (B_got_const ly2)).
  unfold YG0f.cell_holds in HGC. cbn [c_at c_val c_w z8 c8 aeval] in HGC.
  replace a with (STRTOD_GOT_GUARD + Z.of_nat (Z.to_nat (a - STRTOD_GOT_GUARD)))
    by (unfold STRTOD_GOT_GUARD; clear - Ha; lia).
  assert (Hg8 : (Z.to_nat (a - STRTOD_GOT_GUARD) < 8)%nat) by (unfold STRTOD_GOT_GUARD; clear - Ha; lia).
  set (g8 := Z.to_nat (a - STRTOD_GOT_GUARD)) in *. clearbody g8.
  rewrite (HGC g8 Hg8), (YStrtodRowX.srx_got_b_sound segs _ _ g8 strtod_got_A Hg8). cbn [option_map]. f_equal.
  rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
  unfold YG0f.le_byte. rewrite Zmod_mod. reflexivity. }
(* the text's bytes: off the frame's endptr cell and off errno *)
assert (TXTW : forall x, text <= x < text + len -> ~ (fr <= x < fr + 64) /\ ~ (as_errno B <= x < as_errno B + 4)).
{ intros x Hx. destruct (vnt_text_home ly S Hp W mem Lam peak cnt fail ran most own text len x HLED267 HHOME Hx)
    as [(bt & mt & Hbt & Hxt) | (Hi & He)].
  - pose proof (sep_block_frame_x segs B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR Hbt HinF) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite Hfb, <- Hfr in Hd.
    split; [clear - Hd Hxt; lia|].
    destruct (BBAND _ _ (HABS _ _ Hbt)) as [Hl | Hl]; rewrite B_errno; unfold STRTOD_ERRNO; clear - Hl Hxt; lia.
  - split; [|exact He]. intros Hf. exact (frm_img_x segs B ARx LAWS _ _ _ _ _ _ 0 pos x HAR HinF
                                            ltac:(rewrite Hfb, <- Hfr; exact Hf) Hi). }
apply (vrd_seg_271_P B ARx SK LAWS H_checked_memcpy_xm P PLAW PCALL d e q v ly0 S0 Hp0 W0 regs0 mem0 md0 pos ly2 S2
  Hp2 (k + kk) W2 regs2 mem2 md2 sp fr p' n res _ HJ2 HPM2 Q2 Q9 Q19 Q20 Q23 Q27 Q26 R10r Q3 Q4 N8 A3 (proj1 N9) (proj2 N9) Hv4 N15
  (proj1 N16) (proj2 N16) Hres64 (proj1 N17) (proj2 N17) (proj1 N18) (proj1 (proj2 N18)) (proj2 (proj2 N18))
  He0 (proj1 N11) (proj1 N19) Hmod16 (proj2 N19) V16b V24b VQ2 HWN16 RAv24 Amv24 RAq2 Amq8 HCPY).
{ intros regs3 mem3 md3 _ _ _ _ _ _ _ Hr0. exfalso. exact (Hres0 Hr0). }
intros regs4 mem4 md4 HJ4 HPM4 TK4 R25d4 R10d4 KP4 MG4 CPY4 V16r V8s V16s V24s RAv4 RAq4 RAr4 _.
pose proof (vnt_regs1 regs4 regs2 regs TK4 HPR2) as L4.
(* the token, copied into the block *)
assert (TXT4 : garr8 segs (rdW W2 mem4) res txt).
{ intros j Hj.
  assert (Hpt : 0 <= p' - text) by (clear - Hp'r; lia).
  assert (Hjt : (Z.to_nat (p' - text) + j < length tb)%nat).
  { assert (E1 : length (rest_atR tb text p') = (length txt + length r)%nat) by (rewrite Htxt, length_app; reflexivity).
    unfold rest_atR in E1. rewrite length_skipn in E1. clear - E1 Hj. lia. }
  destruct (Hby2 (Z.to_nat (p' - text) + j)%nat Hjt) as [Hv Hb].
  assert (Enth : nth (Z.to_nat (p' - text) + j) tb 0 = nth j txt 0).
  { rewrite <- (firstn_skipn (Z.to_nat (p' - text)) tb) at 1.
    rewrite app_nth2 by (rewrite length_firstn; clear; lia).
    rewrite length_firstn.
    replace (Z.to_nat (p' - text) + j - Nat.min (Z.to_nat (p' - text)) (length tb))%nat with j by (clear - Hjt; lia).
    pose proof Htxt as Ht. unfold rest_atR in Ht. rewrite Ht. apply app_nth1. exact Hj. }
  rewrite Enth in Hv, Hb. split; [|exact Hb].
  apply (vnt_vm_move (w_H W2) (w_H W2) mem2 mem4 (text + Z.of_nat (Z.to_nat (p' - text) + j)) (res + Z.of_nat j) 1);
    [|exact Hv].
  intros ii Hii. assert (Ei : ii = 0%nat) by (clear - Hii; lia). subst ii.
  replace (res + Z.of_nat j + Z.of_nat 0) with (res + Z.of_nat j) by (clear; lia).
  replace (text + Z.of_nat (Z.to_nat (p' - text) + j) + Z.of_nat 0) with (p' + Z.of_nat j) by (clear - Hpt; lia).
  apply CPY4. clear - Hj En; lia. }
assert (GOT4 : forall a, si_got_guard strtod_img_A <= a < si_got_guard strtod_img_A + 8 ->
          aview segs (w_H W2) mem4 a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a))).
{ intros a Ha. rewrite HGG in Ha. destruct (GOT2 a Ha) as (Hi & Hrom).
  pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hl. unfold kLowMemEnd in Hl.
  rewrite (KP4 a ltac:(clear - Hl; lia) ltac:(intros Hx; exact (NIMG a ltac:(clear - Hx; lia) Hi))
             ltac:(clear - Hl HSPlo C1; lia)
             ltac:(intros Hx; exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ _ _ a HAR2 Hin2
                                       ltac:(clear - Hx Hrq Hcf; lia) Hi))
             ltac:(clear - Hl HSPlo C1 HES; lia)).
  exact Hrom. }
assert (P2 : getr regs4 2 = w64 sp) by vnt_rg L4 2 R2'.
assert (P9 : getr regs4 9 = w64 sp) by vnt_rg L4 9 R9'.
assert (P19 : getr regs4 19 = w64 v) by vnt_rg L4 19 R19'.
assert (P23 : getr regs4 23 = w64 SHADOW_OFF) by vnt_rg L4 23 R23'.
assert (P26 : getr regs4 26 = w64 fr) by vnt_rg L4 26 R26'.
assert (P3 : getr regs4 3 = w64 (as_gp B)) by vnt_rg L4 3 Rgp'.
assert (P4 : getr regs4 4 = w64 (as_tp B)) by vnt_rg L4 4 Rtp'.
assert (Q0' : 0 <= q) by (clear - N4 C1; lia).
assert (Q8' : q + 8 <= 2 ^ 47) by (clear - N16; lia).
assert (R4096 : 4096 <= res) by (clear - Rr4 Hcf; lia).
assert (VSP : v + 24 <= sp \/ sp + 32 <= v + 16) by (left; clear - NLO HSPlo; lia).
assert (VRN : v + 24 <= res + n \/ res + n + 1 <= v + 16) by (clear - HC6 N10; lia).
assert (TOK : vrd_txt_ok txt) by (split; [exact Hnum | rewrite <- En; exact Hn30]).
assert (ENDW : forall a, fr + 32 <= a < fr + 32 + 8 ->
          awr_byte (STK_parse_value d + e) (spZ regs0 + e) (rd_fp q v) (ablocks B ly0 S0) (ablocks B ly2 S2) ly2
            [(0, pos)] a \/ wr_fp_frame (rd_fp q v) S0 ly2 a).
{ intros a Ha. left. right. right. right. exists 0, pos. split; [left; reflexivity|].
  left. unfold in_zr. cbn [fst snd]. rewrite EFA, Hfb, <- Hfr. clear - Ha; lia. }
assert (FRS : fr + 40 <= sp - STK_RT_STRTOD) by (clear - HFc HSPS; lia).
assert (AMF : amem_range (fr + 32) 8).
{ unfold amem_range. unfold in_app in HFapp. destruct HFapp as (_ & [Hl | (Hh & _)]);
    [left; clear - Hl C5 HKLS; lia | right; clear - Hh HFc C1 C4; lia]. }
assert (FRB : fr + 40 <= res \/ res + n + 1 <= fr + 32) by (clear - SBF Hrq Hcf; lia).
assert (BND : res + n + 1 <= si_img_lo strtod_img_A \/ si_globals_top strtod_img_A <= res).
{ rewrite HIL, HGT. destruct (BBAND _ _ Hin2) as [Hl | Hl]; [left; clear - Hl Hrq Hcf; lia | right; clear - Hl Hcf; lia]. }
assert (GBND : si_globals_top strtod_img_A <= fr + 32) by (rewrite HGT; clear - FBAND; lia).
apply (vrd_seg_284_P B ARx SK LAWS B_tp B_errno B_errno_own P PLAW PCALL PMN d e q v ly0 S0 Hp0 W0 regs0 mem0 md0
  pos ly2 S2 Hp2 (k + kk) W2 regs4 mem4 md4 sp fr n res txt _ HJ4 HPM4 P2 P9 P19 R25d4 P23 P26 P3 P4
  N8 A3 (proj1 N9) Hv4 N15 Q0' Q8' (eq_sym En) (proj1 N17) R4096 HC1 VSP VRN He0 (proj1 N11) (proj1 N19) Hmod16 N20
  V8s V16s V24s V16r TXT4 HC2 RAv4 Amv24 RAq4 RAr4 HC3 TOK HFZ ENDW FRS AMF FRB BND GBND GOT4).
intros fx' regs5 mem5 md5 bits cc FZ5 FK5 FR5 SM5 Hcc HJ5 HPM5 TK5 R25e KP5 MG5 VE5 TXT5 RAv5 RAq5 RAr5.
pose proof (vnt_regs2 regs5 regs4 regs2 regs TK5 TK4 HPR2) as L5.
(* what rows 271..298 leave alone *)
assert (KH5 : forall a, sp + 32 <= a < 2 ^ 64 -> aview segs (w_H W2) mem5 a = aview segs (w_H W) mem1 a).
{ intros a Ha.
  rewrite (KP5 a ltac:(clear - Ha N8 HP46; lia) ltac:(clear - Ha HC1 HSPlo; lia) ltac:(clear - Ha HFc HSPlo; lia)
             ltac:(clear - Ha; lia) ltac:(rewrite B_errno; unfold STRTOD_ERRNO; clear - Ha HSPlo C1; lia)).
  rewrite (KP4 a ltac:(clear - Ha N8 HP46; lia) ltac:(clear - Ha NLO HSPlo; lia) ltac:(clear - Ha; lia)
             ltac:(clear - Ha HC1 HSPlo; lia) ltac:(clear - Ha; lia)).
  exact (KH2 a Ha). }
assert (KN5 : forall a, v <= a < v + 56 -> ~ (v + 16 <= a < v + 24) ->
          aview segs (w_H W2) mem5 a = aview segs (w_H W) mem1 a).
{ intros a Ha Hn.
  rewrite (KP5 a ltac:(clear - Ha Hv4 NLO C1 HP64; lia) ltac:(clear - Ha NBi Hrq Hcf N10; lia)
             ltac:(clear - Ha FDJ; lia) ltac:(clear - Ha NLO HSPS; lia)
             ltac:(rewrite B_errno; unfold STRTOD_ERRNO; clear - Ha NBAND; lia)).
  rewrite (KP4 a ltac:(clear - Ha Hv4 NLO C1 HP64; lia) Hn ltac:(clear - Ha NLO HSPlo; lia)
             ltac:(clear - Ha NBi Hrq Hcf N10; lia) ltac:(clear - Ha NLO HSPS HES HKS; lia)).
  exact (KN2 a Ha). }
assert (KFR5 : forall a, fr <= a < fr + 64 -> ~ (fr + 32 <= a < fr + 40) ->
          aview segs (w_H W2) mem5 a = aview segs (w_H W) mem1 a).
{ intros a Ha Hn.
  rewrite (KP5 a ltac:(clear - Ha HF4 HFc C1 HP64; lia) ltac:(clear - Ha SBF Hrq Hcf N10; lia) Hn
             ltac:(clear - Ha HFc HSPS; lia) ltac:(rewrite B_errno; unfold STRTOD_ERRNO; clear - Ha FBAND; lia)).
  rewrite (KP4 a ltac:(clear - Ha HF4 HFc C1 HP64; lia) ltac:(clear - Ha FDJ; lia) ltac:(clear - Ha HFc HSPlo; lia)
             ltac:(clear - Ha SBF Hrq Hcf N10; lia) ltac:(clear - Ha HFc HSPS HES HKS; lia)).
  exact (KF2 a Ha). }
assert (V16_5 : val_mem segs (rdW W2 mem5) (v + 16) 8 res).
{ apply (val_mem_kept segs (w_H W2) (w_H W2) mem4 mem5 (v + 16) 8 res); [|exact V16r].
  intros jj Hk. cbn in Hk.
  apply KP5; [clear - Hk Hv4 NLO C1 HP64; lia | clear - Hk HC6 N10; lia | clear - Hk FDJ; lia
             | clear - Hk NLO HSPS; lia | rewrite B_errno; unfold STRTOD_ERRNO; clear - Hk NBAND; lia]. }
(* the ledger at row 299: the allocation's, through the copy, the NUL and strtod *)
assert (HEADX : forall a0 k0 i, In (a0, k0) ((res, n + 1) :: Lam) -> 0 <= i < 8 ->
          ~ (v + 16 <= a0 - cf_head + i < v + 24) /\ ~ (sp + 8 <= a0 - cf_head + i < sp + 16) /\
          ~ (res <= a0 - cf_head + i < res + n + 1) /\ ~ (sp - STK_RT_STRTOD <= a0 - cf_head + i < sp) /\
          ~ (fr + 32 <= a0 - cf_head + i < fr + 40) /\ ~ (as_errno B <= a0 - cf_head + i < as_errno B + 4)).
{ intros a0 k0 i Hin Hi.
  destruct (prh_ledger_hblock B _ _ _ _ _ _ _ _ _ _ a0 k0 _ _ HLDs Hin) as (Hk0 & Hab & _).
  destruct (alx_blocks segs B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 _ _ HAR2 Hab) as (_ & H4096 & Hcb & _).
  assert (Hrk : k0 + cf_head <= req_size (k0 + cf_head))
    by (unfold req_size; destruct (Z.eqb_spec (k0 + cf_head) 0) as [E0|E0]; clear - Hk0 Hcf E0; lia).
  split.
  { intros Hx. pose proof NODEH as NH. unfold vnt_hide in NH.
    destruct NH as [(bn & mn & Hbn & Hb1 & Hb2 & Hbl) | (cidn & posn & Hfn & Hf1 & Hf2)].
    - assert (Hxr : bn <= a0 - cf_head + i < bn + req_size mn) by (clear - Hx Hb1 Hb2; lia).
      assert (Hpr : (bn, mn) = (a0 - cf_head, k0 + cf_head) -> a0 <= a0 - cf_head + i).
      { intros E. destruct Hin as [E' | Hin'].
        + injection E' as <- <-. exfalso. apply Hfresh. rewrite <- E. exact Hbn.
        + pose proof (Hbl a0 k0 Hin' E) as Ha0. clear - Ha0 Hx; lia. }
      exact (vnt_head_off ly2 S2 Hp2 W2 mem2 md2 bn mn a0 k0 i (a0 - cf_head + i) HAR2 (HABS bn mn Hbn) Hab Hk0 Hi
               Hxr Hpr eq_refl).
    - assert (Hxr : frame_addr ly2 cidn posn <= a0 - cf_head + i < frame_addr ly2 cidn posn + fs_frame_bytes cidn)
        by (rewrite EFA; clear - Hx Hf1 Hf2; lia).
      assert (Hfn2 : In (cidn, posn) (frames S2)) by (rewrite Hfrsc; exact Hfn).
      exact (vnt_head_off_frame ly2 S2 Hp2 W2 mem2 md2 cidn posn a0 k0 i (a0 - cf_head + i) HAR2 Hfn2 Hab Hk0 Hi
               Hxr eq_refl). }
  split; [clear - Hcb Hrk Hi Hk0 HW8 HSPlo; lia|].
  split.
  { destruct Hin as [E | Hin'].
    - injection E as <- <-. clear - Hi HW8; lia.
    - assert (Hne : (a0 - cf_head, k0 + cf_head) <> (res - cf_head, n + 1 + cf_head)).
      { intros E. injection E as E1 _. apply RrL. apply in_map_iff. exists (a0, k0).
        split; [cbn [fst]; clear - E1; lia | exact Hin']. }
      pose proof (sep_blocks_x segs B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR2 Hab Hin2 Hne) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. clear - Hd Hi Hrk Hrq Hk0 HW8 Hcf; lia. }
  split; [clear - Hcb Hrk Hi Hk0 HW8 HSPS; lia|].
  split.
  { pose proof (sep_block_frame_x segs B ARx LAWS _ _ _ _ _ _ _ _ _ _ HAR2 Hab HinF2) as Hd.
    unfold zdisjoint in Hd. cbn [fst snd] in Hd. rewrite EFA, Hfb, <- Hfr in Hd. clear - Hd Hi Hrk Hk0 HW8; lia. }
  destruct (BBAND _ _ Hab) as [Hl | Hl]; rewrite B_errno; unfold STRTOD_ERRNO; clear - Hl Hi Hrk Hk0 HW8; lia. }
assert (HLED5 : prh_ledger B ly2 S2 Hp2 W2 mem5 ((res, n + 1) :: Lam) (Z.max peak (Ledger.lsum Lam + (n + 1)))
                  ((cnt + 1) mod 2 ^ 64) fail ran most own).
{ apply (vnt_ledger_keep_pst ly2 S2 Hp2 W2 mem2 mem5 mem2 md2 _ _ _ _ _ most own
    (fun a => (v + 16 <= a < v + 24) \/ (sp + 8 <= a < sp + 16) \/ (res <= a < res + n + 1) \/
              (sp - STK_RT_STRTOD <= a < sp) \/ (fr + 32 <= a < fr + 40) \/ (as_errno B <= a < as_errno B + 4))
    HAR2 HLDs).
  - intros a Ha Hx.
    rewrite (KP5 a Ha ltac:(intros H'; apply Hx; right; right; left; clear - H' N10; lia)
               ltac:(intros H'; apply Hx; do 4 right; left; exact H') ltac:(intros H'; apply Hx; do 3 right; left; exact H')
               ltac:(intros H'; apply Hx; do 5 right; exact H')).
    apply (KP4 a Ha ltac:(intros H'; apply Hx; left; exact H') ltac:(intros H'; apply Hx; right; left; exact H')
             ltac:(intros H'; apply Hx; right; right; left; clear - H'; lia)
             ltac:(intros H'; apply Hx; do 3 right; left; clear - H' HES HKS; lia)).
  - intros a Ha Hx. pose proof (PST_IMG a Ha) as Hi. pose proof (@pa_segs_low _ _ PI_prog_A a Hi) as Hl.
    unfold kLowMemEnd in Hl.
    destruct Hx as [Hx | [Hx | [Hx | [Hx | [Hx | Hx]]]]].
    + exact (NIMG a ltac:(clear - Hx; lia) Hi).
    + clear - Hx Hl HSPlo C1; lia.
    + exact (blk_img_x segs B ARx LAWS _ _ _ _ _ _ _ _ a HAR2 Hin2 ltac:(clear - Hx Hrq Hcf; lia) Hi).
    + clear - Hx Hl HSPS C1; lia.
    + exact (frm_img_x segs B ARx LAWS _ _ _ _ _ _ 0 pos a HAR HinF ltac:(rewrite Hfb, <- Hfr; clear - Hx; lia) Hi).
    + exact (PST_ERRNO a Ha Hx).
  - intros a0 k0 i Hin Hi Hx. destruct (HEADX a0 k0 i Hin Hi) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
    destruct Hx as [Hx | [Hx | [Hx | [Hx | [Hx | Hx]]]]]; contradiction. }
(* the boundary at row 299, then WalkNumEnd's end segment at P *)
assert (H299 : vrd_num299_a (fx := fx) B ARx SK ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt
                 fail ran most own W2
                 (cfg_at (fx := fx') segs (BASE + vrd_row 299) regs5 mem5 md5)).
{ exists fx', W, pos, p', k1, (k + kk), ly, ly2, S, S2, Hp, Hp2, regs1, mem1, md1, regs5, mem5, md5, txt, r, res, bits,
    cc, sp, fr.
  split; [reflexivity|].
  split; [exact FZ5|]. split; [exact FK5|].
  (* vrd_num299_a's fpre, rd_pre and dispatch body read the float state BOUND by its first existential (their
     implicit fx resolved to fx2 in the definition): their only float-state conjunct is frm_zero (fpre's last, the
     kit's FRM0-ENTRY; rd_pre's first; vrd_disp_body's last), which strtod's post gives *)
  split; [destruct HPRE as (FPa & FPb & FPc & FPd & _); exact (conj FPa (conj FPb (conj FPc (conj FPd FZ5))))|].
  split; [exact R10q|]. split; [exact R11v|].
  split; [split; [exact FZ5 | exact (proj2 HRD)]|].
  split.
  { pose proof HB as HB'. unfold vrd_disp_body in HB' |- *.
    repeat match type of HB' with ?A /\ ?R => let H1 := fresh "HBc" in destruct HB' as [H1 HB']; split; [exact H1|] end.
    (* the loop stops at frm_zero (read at fx there, at fx' here); the three cut conjuncts after it read no float
       state *)
    split; [exact FZ5 | exact (proj2 HB')]. }
  split; [exact Htok|]. split; [exact Hrest|].
  split; [exact Cnf|]. split; [exact Rr4|]. split; [exact Rr16|]. split; [exact RrL|]. split; [exact HHr|].
  split; [rewrite HA, <- En; reflexivity|].
  split; [exact HRL2|].
  split; [pose proof HHU0 as HHU1; rewrite Hgt in HHU1; exact HHU1|].
  split; [rewrite <- En; exact HLED5|].
  split; [exact HJ5|].
  split; [rewrite Hfrsc; exact HFr|].
  split; [intros a Ha Hn; rewrite (KH5 a (WB a Ha)); exact (HWIN a Ha Hn)|].
  split; [exact SM5|]. split; [rewrite <- En; exact Hcc|]. split; [exact FR5|]. split; [exact VE5|].
  split; [rewrite EFA; reflexivity|]. split; [reflexivity|].
  split; [vnt_rg L5 2 R2'|]. split; [vnt_rg L5 9 R9'|]. split; [vnt_rg L5 8 R8'|].
  split; [vnt_rg L5 18 R18'|]. split; [vnt_rg L5 26 R26'|]. split; [vnt_rg L5 24 R24'|].
  split; [exact R25e|].
  split; [vnt_rg L5 19 R19'|]. split; [vnt_rg L5 20 R20'|]. split; [vnt_rg L5 23 R23'|]. split; [vnt_rg L5 27 R27'|].
  split; [vnt_rg L5 21 R21|].
  split; [vnt_rg L5 22 (eq_trans R22 (f_equal (fun x => w64 (p' + x)) En))|].
  split; [vnt_rg L5 3 (eq_trans Rgp' (eq_sym Rgp0))|]. split; [vnt_rg L5 4 (eq_trans Rtp' (eq_sym Rtp0))|].
  split; [exact N8|]. split; [exact A3|]. split; [clear - HSPhi; lia|].
  split; [exact V16_5|].
  split; [exact TXT5|].
  destruct HFRAME as (VF0 & VF16 & VF56 & _).
  split; [apply (val_mem_kept segs (w_H W) (w_H W2) mem1 mem5 fr 8 _); [|exact VF0];
          intros jj Hk; cbn in Hk; apply KFR5; clear - Hk; lia|].
  split; [apply (val_mem_kept segs (w_H W) (w_H W2) mem1 mem5 (fr + 16) 8 _); [|exact VF16];
          intros jj Hk; cbn in Hk; apply KFR5; clear - Hk; lia|].
  split; [rewrite EFL; apply (val_mem_kept segs (w_H W) (w_H W2) mem1 mem5 (fr + 56) 8 _); [|exact VF56];
          intros jj Hk; cbn in Hk; apply KFR5; clear - Hk; lia|].
  split.
  { pose proof HSAV as HS'. unfold vrd_saved in HS' |- *.
    destruct HS' as (V1 & V2 & V3 & V4 & V5 & V6 & V7 & V8 & V9 & V10 & V11 & V12 & V13).
    repeat split; (eapply val_mem_kept; [|eassumption]); intros jj Hk; cbn in Hk; apply KH5;
      clear - Hk HSPhi Hshi0 H470 HP47 HP64; lia. }
  split; [exact RAv5|]. split; [exact RAq5|]. split; [rewrite <- En; exact RAr5|].
  split.
  { split; [apply (vnt_vm_move (w_H W) (w_H W2) mem1 mem5 q q 8 p'); [|exact Vq];
            intros jj Hk; apply KH5; apply QB; clear - Hk; lia|].
    split; [apply (vnt_vm_move (w_H W) (w_H W2) mem1 mem5 (q + 8) (q + 8) 8 _); [|exact Vq8];
            intros jj Hk; apply KH5; apply QB; clear - Hk; lia|].
    split; [apply (vnt_vm_move (w_H W) (w_H W2) mem1 mem5 (q + 16) (q + 16) 4 _); [|exact Vq16];
            intros jj Hk; apply KH5; apply QB; clear - Hk; lia|].
    split; [apply (vnt_rw_xfer (w_H W) (w_H W2) mem1 mem5 q 24); [exact QIMG | | exact Hrwq];
            intros x Hx; apply KH5; exact (QB x Hx)|].
    split; [exact Hq8|]. split; [exact Ht0|]. split; [exact Htl|]. split; [exact Hp'r|]. split; [exact Hlen|].
    split.
    { apply (vnt_garr8_xfer (w_H W2) (w_H W2) mem2 mem5 text tb); [|exact Hby2].
      intros x Hx. rewrite Hlen in Hx. destruct (TXTW x Hx) as (Tf & Te).
      rewrite (KP5 x ltac:(clear - Hx Ht4 Hc82 C1 HP64; lia) ltac:(clear - Hx TBi Hrq Hcf N10; lia)
                 ltac:(clear - Tf; lia) ltac:(clear - Hx Hc82 HSPS; lia) Te).
      apply (KP4 x ltac:(clear - Hx Ht4 Hc82 C1 HP64; lia) ltac:(clear - Hx Htv'; lia) ltac:(clear - Hx Hc82 HSPlo; lia)
               ltac:(clear - Hx TBi Hrq Hcf N10; lia) ltac:(clear - Hx Hc82 HSPS HES HKS; lia)). }
    split; [exact Hqt|]. exact Hd32. }
  split.
  { split; [exact Hv8|]. apply vnt_rw_of_view. intros x Hx.
    split; [clear - Hx Hv4 NLO C1 HP64; lia|]. split; [exact (NIMG x Hx)|].
    destruct (Z_lt_le_dec x (v + 16)) as [Hl | Hl]; [|destruct (Z_lt_le_dec x (v + 24)) as [Hm | Hm]].
    - rewrite (KN5 x Hx ltac:(clear - Hl; lia)), (NZ1 x Hx). discriminate.
    - exact (vnt_vm_some (w_H W2) mem5 (v + 16) 8 res x V16_5 ltac:(change (Z.of_nat 8) with 8; clear - Hl Hm; lia)).
    - rewrite (KN5 x Hx ltac:(clear - Hm; lia)), (NZ1 x Hx). discriminate. }
  split; [intros a Ha Hn; rewrite (KN5 a Ha Hn); exact (NZ1 a Ha)|].
  (* THE POSITION TRANSFER and THE LIVE SET across the granted malloc, from S0 (the frame take S = set_fs f S0) *)
  split.
  { pose proof (HT1 Hres0) as HT1'. rewrite HSf, En in HT1'.
    exact (vnt_transfer_alloc S0 f S2 (length txt) HI_head HT1'). }
  split.
  { pose proof HA as HA'. rewrite HSf, En in HA'.
    exact (vnt_live_alloc ly S0 f ly2 S2 (res - cf_head) (length txt) HI_head HA'). }
  intros a Ha. apply HWN. clear - Ha; lia. }
exact (H_num_end P PLAW ly0 S0 Hp0 W0 regs0 mem0 md0 ch CTX0 CW e q v text len p d tb Lam peak cnt fail ran most own
  W2 _ H299 HPM5).
Qed.

End n.
