(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Theorem Labs, 2026-10: fuzz_preset, image A' (#102 asan 1be0f53d, twin bff8519b), ex_value piece 5 (ev_number,
   fuzz_preset.c fa3e896698eb :243-264 (#102 source) inlined): the piece's INTERNAL cut points, over WalkS8a's interface S8aIface.v
   (ev_act, ev_mid, ev_regs, ev_at_kind, ev_to_exit, ev_number_spec), and the strtod call's premises in the words of
   the strtod ROW (lib/Reusable/YStrtodRowX.v astrtod_realizes_x, h-verbs-1; it closes gap EX-STRTOD-END of
   PRH_FnEx.v). Statements only.

   Cuts (offset from ex_value's entry; LENGTH, measured from the internal file ex_value.fuzz_preset.asan.s):
     EV_NUM  +0x2c4 (0x83568)  ev_at_kind (WalkS8a's)
     CL      +0x364 (0x83608)  the scan loop's head, s6 = a0 = x0 + j
     CS      +0x8c0 (0x83b64)  the scan's end at j
     CR      +0x924 (0x83bc8)  strtod's return site
     CC      +0x958 (0x83bfc)  the number is whole and finite; the num slot holds its bits
     CD      +0x9e4 (0x83c88)  in->differs decided
     CT      +0x9f4 (0x83c98)  the common tail, s5 = r
     EV_EXIT +0xaa4 (0x83d48)  ev_to_exit (WalkS8a's)
   Sub-pieces (each proves `cut -> SRr segs W (ev_cfg fxc regs off mem md) (ev_to_exit a)` from the next cuts'):
   A = EV_NUM -> CT | CL; B = CL -> CS (the loop); C = CS -> CR (__asan_memcpy, the NUL, strtod); D = CR -> CT | CC
   (fsd, *end, fclass.d); E = CC -> CD (v: type, __wrap_strcmp, __wrap_bcmp); F = CD -> CT; T = CT -> EV_EXIT.

   Numerals: offsets into ex_value (LENGTH, measured); 24 / 32 / 64 / 96 / 104 / 112 / 120 (LENGTH: struct ex field
   offsets, frame slots of `end` / `num`, s1-relative spills, from the listing); 45 48 (WORD, ASCII '-' '0');
   -1 -11 58 288230376218820621 (WORD: immediates / the value the listing builds at +0x34c..+0x360 = 2^58+2^26+13);
   2 ^ 30, 2 ^ 62
   (LENGTH, plain strtod_c.v's bounds); register numbers (WORD). No ADDRESS.

   MEMNORM (h-w6u-pre 13:0xZ, the SEG_N method of lib/B/Prog/PvB_NCut.v): YAkMemnorm.memnorm segs mem is a STATE fact,
   not a law. It is ev_mid's LAST conjunct (S8aIface.v, h-walk-ctrl's text, 13:01Z), so every cut carries it through
   MID: seeded at EV_NUM by ev_at_kind's MID, kept across runs and hand steps by lib/Reusable/YSRrMemnorm.v's *_inv
   twins, across calls by the keep conjuncts of the texts below (aintrin_realizes_xm, abcmp_realizes_xm,
   astrcmp_realizes_xrom: YGcallMxmn.v; astrtod_realizes_x: YStrtodRowX.v's post keep). The refuted universal law
   ev_memnorm_law is deleted; lane M's statements take memnorm of the new memory as a premise. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import
YK11 YK0s YK0o YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YGcfNames YCbqG YP0b YPsym YC4aP FCiface YGcallMx YGcallMxmn.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YStrtodRowX YAkMemnorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Ledger.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import PRH_Base PRH_FnEx.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A.Prog Require Import S8aIface.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PjTree PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require PjStruct ReaderRes strtod_c.
Import ListNotations.
Local Open Scope Z_scope.

(* ---- pure: the text pieces the code computes ---- *)
(* the number arm's reading of the text from the dispatch byte (PjGrammar.jr_number at ReaderRes.jr_strtod) *)
Definition ev_N (xs : list Z) : option (PjTree.jv * list Z) :=
  fst (fst (PjGrammar.jr_number ReaderRes.jr_strtod xs [])).
(* the sign: 1 when the first byte is '-' *)
Definition ev_sg (c : Z) : nat := if c =? 45 then 1%nat else 0%nat.
(* the bytes [a, z) of x *)
Definition ev_sub (x : list Z) (a z : nat) : list Z := firstn (z - a) (skipn a x).
(* fuzz_preset.c :224 passes at j0 = i1 + sg *)
Definition ev_lead_ok (x : list Z) (j0 : nat) : Prop :=
  (j0 < length x)%nat /\ PjGrammar.digit (nth j0 x 0) = true /\
  ~ (nth j0 x 0 = 48 /\ (S j0 < length x)%nat /\ PjGrammar.digit (nth (S j0) x 0) = true).

(* the texts strtod is called with: number characters, shorter than 2 ^ 30 (the row's txt_ok; the bound is plain
   strtod_c.v's) *)
Definition ev_txt_ok (txt : list Z) : Prop :=
  Forall (fun z => PjGrammar.numch z = true) txt /\ Z.of_nat (length txt) < 2 ^ 30.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams} {PI : PrhImg}
  {RL : PrhRoomLive}.
Context {L : ptable asym} {PA : PAImg L}.
Local Notation segs := pa_segs.
Variable B : asyms.
Variable ARx : alayout -> astate -> list Z -> world segs -> (word -> option byte) -> Model -> Prop.
Variable SK : YI16.sink_head.
#[local] Abbreviation rdW W mem := (mrestrict (w_H W) mem).

(* ---- the strtod call's caller facts that neither AR_laws_x (YCbqG.v:149-166) nor ev_pre gives; the row's
   strtod_site_x (YStrtodRowX.v:347-352) asks them. Each is a Section hypothesis of ev_number (S8aNumber.v). ---- *)
(* (the MARKED entry law ev_memnorm_law is deleted: memnorm is ev_mid's last conjunct, a state fact; see the header) *)
(* strtod_site_x's text clause: a live block lies off the image band [si_img_lo, si_globals_top). AR_laws_x has no
   such law (alx_client_img keeps a block out of ly_img and in_img only; at AR it is YC1fP.v:334 blk_off_imgPI, from
   ALedger's pa_img_cover). *)
Definition ev_blk_offimg (I : YStrtodRowX.strtod_img) : Prop :=
  forall ly S Hp W mem md p n, ARx ly S Hp W mem md -> In (p, n) (ablocks B ly S) ->
  p + req_size n <= YStrtodRowX.si_img_lo I \/ YStrtodRowX.si_globals_top I <= p.
(* strtod_site_x's end-cell clause: a live fake frame lies above the image's globals (si_globals_top <= e) *)
Definition ev_frm_offimg (I : YStrtodRowX.strtod_img) : Prop :=
  forall ly S Hp W mem md cid pos, ARx ly S Hp W mem md -> In (cid, pos) (frames S) ->
  YStrtodRowX.si_globals_top I <= frame_addr ly cid pos.
(* strtod_site_x's GOT clause, in the SEG_N form (lib/B/Prog/PvB_ND.v IMG_GOTV / IMG_GOTC). PValueB's audit (10:11Z)
   found the old form (the guard bytes are not runtime-owned statics) FALSE at image B, where the guard word is in
   Tfib_owned_static; image A's guard is the same kind of cell (A/AE22.v A_GOT_CANARY), so piece 5 takes the same form.
   the guard word hold the guard cell's address (image fact: A/Prog/strtod_row.v strtod_got_A at PI_prog_A); (2) the
   guard word is one of B's const cells (image-A binding: A/AE22.v canary_cell_in), which AR_laws_x field 16
   alx_const_cells keeps in every ARx state. Together they give the rom view of the guard bytes at any call memory. *)
Definition ev_got_ok (I : YStrtodRowX.strtod_img) : Prop :=
  YStrtodRowX.srx_got_b segs (YStrtodRowX.si_got_guard I) (YStrtodRowX.si_guard I) = true /\
  forall ly, In (z8 (ANum (YStrtodRowX.si_got_guard I)) (YStrtodRowX.si_guard I)) (as_const B ly).
Definition ev_strtod_site (I : YStrtodRowX.strtod_img) : Prop :=
  ev_blk_offimg I /\ ev_frm_offimg I /\ ev_got_ok I.

Section e.
Variable a : ev_act.
Let x := ea_x a.
Let len := ea_len a.
Let x0 := ea_x0 a.
Let fr := ea_fr a.
Let S1 := ea_S1 a.
Let q := ea_q a.
Local Notation MID := (ev_mid B ARx SK a).
Local Notation SRX W fxc regs off mem md := (SRr segs W (ev_cfg fxc regs off mem md) (@ev_to_exit fx rc cp PI RL L PA B ARx SK a)).

(* every cut after EV_NUM: the dispatch facts of ev_at_kind (byte c at i1, skip), the regs set, s7 = the frame,
   s1 + 104 = v (+0x2c4) *)
Definition ev_base (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (i1 : nat) (c : Z) : Prop :=
  ev_regs a regs /\ getr regs 23 = w64 fr /\
  (i1 < length x)%nat /\ nth i1 x 0 = c /\ PjGrammar.ws c = false /\
  PjGrammar.skip (skipn (Z.to_nat (ea_i0 a)) x) = skipn i1 x /\
  c <> 34 /\ c <> 91 /\ c <> 123 /\ c <> 102 /\ c <> 110 /\ c <> 116 /\
  val_mem segs (rdW W mem) (S1 + 104) 8 (ea_v a).

(* the scan's carriers (+0x268 .. +0x3a0): s11 = &end, s1 + 112 = &num, s5 = -1, a1 = x0 + i1, a2 = x0 + len *)
Definition ev_scanregs (W : world segs) (regs : bvmap 5 word) (mem : word -> option byte) (i1 : nat) : Prop :=
  getr regs 27 = w64 (fr + 32) /\ val_mem segs (rdW W mem) (S1 + 112) 8 (fr + 64) /\ getr regs 21 = w64 (-1) /\
  getr regs 11 = w64 (x0 + Z.of_nat i1) /\ getr regs 12 = w64 (x0 + len).
(* the frame's own `end` (fr+32) and `num` (fr+64) slots have shadow 0 (opened by the prologue at 0x831fc / 0x83200,
   shadow bytes shadow_addr fr + 4 and + 8), carried from CL to CC; both lie in ev_wz so lane M's statements are
   unchanged. Lane A establishes them; B/C/D carry them; D (the *end read, the num fsd) and E (the bcmp on num) use them. *)
Definition ev_fsh (W : world segs) (mem : word -> option byte) : Prop :=
  aview segs (w_H W) mem (shadow_addr fr + 4) = Some 0 /\ aview segs (w_H W) mem (shadow_addr fr + 8) = Some 0.

(* the span facts: lead byte ok at j0 = i1 + sg, [j0, j) numeric *)
Definition ev_span (i1 : nat) (c : Z) (j : nat) : Prop :=
  ev_lead_ok x (i1 + ev_sg c) /\ Forall (fun z => PjGrammar.numch z = true) (ev_sub x (i1 + ev_sg c) j).

(* CL, +0x364 *)
Definition ev_CL W regs mem md ly S Hp k (i1 : nat) (c : Z) (j : nat) : Prop :=
  MID ly S Hp W mem md k (x0 + Z.of_nat i1) (ea_dep a) (ea_dl a) /\ ev_base W regs mem i1 c /\
  ev_scanregs W regs mem i1 /\ ev_span i1 c j /\ (i1 + ev_sg c <= j < length x)%nat /\
  getr regs 22 = w64 (x0 + Z.of_nat j) /\ getr regs 10 = w64 (x0 + Z.of_nat j) /\
  getr regs 13 = w64 (-11) /\ getr regs 14 = w64 58 /\ getr regs 15 = w64 288230376218820621 /\ ev_fsh W mem.

(* CS, +0x8c0: the scan ended at j (the end, or a non-number byte) *)
Definition ev_CS W regs mem md ly S Hp k (i1 : nat) (c : Z) (j : nat) : Prop :=
  MID ly S Hp W mem md k (x0 + Z.of_nat i1) (ea_dep a) (ea_dl a) /\ ev_base W regs mem i1 c /\
  ev_scanregs W regs mem i1 /\ ev_span i1 c j /\ (i1 + ev_sg c < j <= length x)%nat /\
  (j = length x \/ PjGrammar.numch (nth j x 0) = false) /\
  getr regs 22 = w64 (x0 + Z.of_nat j) /\ ev_fsh W mem.

(* CR, +0x924: strtod returned; txt = x[i1, j); the scratch holds txt ++ [0]; *end = scr + cn; fa0 = bits;
   s1 + 120 = &in->scratch, s1 + 96 = its shadow byte's address *)
Definition ev_CR (fxc : YK11.FPState) W regs mem md ly S Hp k (i1 : nat) (c : Z) (j : nat) (bits cn : Z) : Prop :=
  let txt := ev_sub x i1 j in
  MID ly S Hp W mem md k (x0 + Z.of_nat i1) (ea_dep a) (ea_dl a) /\ ev_base W regs mem i1 c /\
  getr regs 27 = w64 (fr + 32) /\ val_mem segs (rdW W mem) (S1 + 112) 8 (fr + 64) /\ getr regs 21 = w64 (-1) /\
  val_mem segs (rdW W mem) (S1 + 120) 8 (q + 24) /\ val_mem segs (rdW W mem) (S1 + 96) 8 (shadow_addr (q + 24)) /\
  ev_span i1 c j /\ (i1 + ev_sg c < j <= length x)%nat /\
  (j = length x \/ PjGrammar.numch (nth j x 0) = false) /\
  getr regs 22 = w64 (x0 + Z.of_nat j) /\
  garr8 segs (rdW W mem) (ea_scr a) (txt ++ [0]) /\
  strtod_c.strtod_model txt = Some (bits, cn) /\ 0 <= cn <= Z.of_nat (length txt) /\
  val_mem segs (rdW W mem) (fr + 32) 8 (ea_scr a + cn) /\
  LinuxProcessSemantics.Riscv.Sem.reg_get (@YK11.fp_regs fxc) (Z_to_bv 5 10) = Z_to_bv 64 bits /\ ev_fsh W mem.

(* CC, +0x958: u = JNum txt bits is read (whole and finite); the num slot holds bits *)
Definition ev_CC W regs mem md ly S Hp k (i1 : nat) (c : Z) (j : nat) (bits : Z) : Prop :=
  let txt := ev_sub x i1 j in
  MID ly S Hp W mem md k (x0 + Z.of_nat i1) (ea_dep a) (ea_dl a) /\ ev_base W regs mem i1 c /\
  val_mem segs (rdW W mem) (S1 + 112) 8 (fr + 64) /\ getr regs 21 = w64 (-1) /\
  val_mem segs (rdW W mem) (S1 + 120) 8 (q + 24) /\ val_mem segs (rdW W mem) (S1 + 96) 8 (shadow_addr (q + 24)) /\
  getr regs 22 = w64 (x0 + Z.of_nat j) /\ (i1 < j <= length x)%nat /\
  ev_N (skipn i1 x) = Some (PjTree.JNum txt bits, skipn j x) /\
  garr8 segs (rdW W mem) (ea_scr a) (txt ++ [0]) /\
  val_mem segs (rdW W mem) (fr + 64) 8 bits /\ ev_fsh W mem.

(* CD, +0x9e4: in->differs decided *)
Definition ev_CD W regs mem md ly S Hp k (i1 : nat) (c : Z) (j : nat) (u : PjTree.jv) : Prop :=
  ev_base W regs mem i1 c /\ getr regs 22 = w64 (x0 + Z.of_nat j) /\ (i1 < j <= length x)%nat /\
  ev_N (skipn i1 x) = Some (u, skipn j x) /\
  exists dl', MID ly S Hp W mem md k (x0 + Z.of_nat i1) (ea_dep a) dl' /\ (dl' = 0 \/ dl' = 1) /\
    (dl' = 1 <-> ea_dl a = 1 \/ (ea_v a <> 0 /\ ea_t a <> u)).

(* CT, +0x9f4: the common tail, s5 = r; the cursor per the number arm's reading *)
Definition ev_CT W regs mem md ly S Hp k (i1 : nat) (c : Z) : Prop :=
  ev_base W regs mem i1 c /\
  exists r p' dl', getr regs 21 = w64 r /\ MID ly S Hp W mem md k (x0 + p') (ea_dep a) dl' /\ (dl' = 0 \/ dl' = 1) /\
    match ev_N (skipn i1 x) with
    | None => r = -1 /\ p' = Z.of_nat i1 /\ dl' = ea_dl a
    | Some (u, rest) => r = 0 /\ p' = len - Z.of_nat (length rest) /\
        (dl' = 1 <-> ea_dl a = 1 \/ (ea_v a <> 0 /\ ea_t a <> u))
    end.

(* ---- the sub-piece statements ---- *)
Definition KT : Prop := forall fxc W regs mem md ly S Hp k i1 c,
  @ev_pre fx rc cp PI L PA B ARx a -> @ev_fx fx fxc -> ev_CT W regs mem md ly S Hp k i1 c -> SRX W fxc regs 0x9f4 mem md.
Definition KL : Prop := forall fxc W regs mem md ly S Hp k i1 c j,
  @ev_pre fx rc cp PI L PA B ARx a -> @ev_fx fx fxc -> ev_CL W regs mem md ly S Hp k i1 c j -> SRX W fxc regs 0x364 mem md.
Definition KS : Prop := forall fxc W regs mem md ly S Hp k i1 c j,
  @ev_pre fx rc cp PI L PA B ARx a -> @ev_fx fx fxc -> ev_CS W regs mem md ly S Hp k i1 c j -> SRX W fxc regs 0x8c0 mem md.
Definition KR : Prop := forall fxc W regs mem md ly S Hp k i1 c j bits cn,
  @ev_pre fx rc cp PI L PA B ARx a -> @ev_fx fx fxc -> ev_CR fxc W regs mem md ly S Hp k i1 c j bits cn -> SRX W fxc regs 0x924 mem md.
Definition KC : Prop := forall fxc W regs mem md ly S Hp k i1 c j bits,
  @ev_pre fx rc cp PI L PA B ARx a -> @ev_fx fx fxc -> ev_CC W regs mem md ly S Hp k i1 c j bits -> SRX W fxc regs 0x958 mem md.
Definition KD : Prop := forall fxc W regs mem md ly S Hp k i1 c j u,
  @ev_pre fx rc cp PI L PA B ARx a -> @ev_fx fx fxc -> ev_CD W regs mem md ly S Hp k i1 c j u -> SRX W fxc regs 0x9e4 mem md.
Definition KN : Prop := forall fxc W regs mem md ly S Hp k i1 c,
  @ev_pre fx rc cp PI L PA B ARx a -> @ev_fx fx fxc -> ev_at_kind B ARx SK a W regs mem md ly S Hp k i1 c ->
  c <> 34 -> c <> 91 -> c <> 123 -> c <> 102 -> c <> 110 -> c <> 116 -> SRX W fxc regs EV_NUM mem md.

(* ---- ev_mid across the piece's own writes (lane M proves these; the other lanes cite them) ----
   the bytes the piece and its callees may change outside the cursor: the callee windows below sp and the s1 spills
   (S1 - STK_RT_STRTOD .. S1 + 128, below the save area at SA + 152), the frame's `end` and `num` slots and their
   shadow bytes, the scratch, errno *)
Definition ev_wz (z : Z) : Prop :=
  S1 - STK_RT_STRTOD <= z < S1 + 128 \/ fr + 32 <= z < fr + 40 \/ fr + 64 <= z < fr + 72 \/
  z = shadow_addr fr + 4 \/ z = shadow_addr fr + 8 \/ ea_scr a <= z < ea_scr a + len + 1 \/
  as_errno B <= z < as_errno B + 4.
Local Notation AJ ly S Hp W mem md k := (ajournal_x (SK := SK) segs B prh_pst ARx (ea_STK a + ea_d a) (ea_sp0 a + ea_d a)
  (ea_FP a) (ea_ly a) (ea_S a) (ea_Hp a) (ea_W a) (ea_mem a) (ea_md a) [(1, ea_pos a)] ly S Hp W mem md k).
(* the cursor unchanged *)
Definition ev_mid_keep_stmt : Prop :=
  forall ly S Hp W mem md k p dep dl mem' md' k',
  @ev_pre fx rc cp PI L PA B ARx a -> MID ly S Hp W mem md k p dep dl -> AJ ly S Hp W mem' md' k' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ ev_wz z -> aview segs (w_H W) mem' z = aview segs (w_H W) mem z) ->
  YAkMemnorm.memnorm segs mem' ->
  MID ly S Hp W mem' md' k' p dep dl.
(* the cursor's in->p and in->differs rewritten (+0x9f0, +0x9e0) *)
Definition ev_mid_cur_stmt : Prop :=
  forall ly S Hp W mem md k p dep dl mem' md' k' p' dl',
  @ev_pre fx rc cp PI L PA B ARx a -> MID ly S Hp W mem md k p dep dl -> AJ ly S Hp W mem' md' k' ->
  (forall z, 0 <= z < 2 ^ 64 -> ~ ev_wz z -> ~ (q <= z < q + 8) -> ~ (q + 32 <= z < q + 36) ->
     aview segs (w_H W) mem' z = aview segs (w_H W) mem z) ->
  prhex_cur W mem' q p' (x0 + len) dep (ea_scr a) dl' ->
  YAkMemnorm.memnorm segs mem' ->
  MID ly S Hp W mem' md' k' p' dep dl'.
End e.

(* the one image fact the generic PrhImg does not bound: ex_value's own frame is at least the 272 bytes
   prh_img_A measures (PRH_Img.v:35). Lanes that write the s1 spills or the fake frame need S1 above alloc_ceiling
   and the frame slots apart from the spills; strtod (lane C) needs ly_stk_lo + STK_RT_STRTOD <= S1. Discharged at
   the concrete instance by reflexivity. *)
Definition ev_img_ok : Prop := 272 <= pi_frame F_ex_value.
Definition ev_A_stmt : Prop := ev_img_ok -> forall a, KT a -> KL a -> KN a.
Definition ev_B_stmt : Prop := forall a, KS a -> KL a.
(* the errno-in-image fact (the middle conjunct of api_env, YCbq.v:810; the instance gets it from PALib pal_env):
   needed to rebuild the journal after strtod, which may change errno. Discharged at the concrete instance.
   strtod: the ROW's call-site text (YStrtodRowX.v:354 astrtod_realizes_x) at strtod's entry, for an image I of the
   row's constants (at image A: lib/A/Prog/strtod_row.v strtod_img_A, the text strtod_row_A), with the caller facts
   ev_strtod_site I that the walk cannot derive. *)
Definition ev_C_stmt : Prop :=
  ev_img_ok ->
  (forall a0, as_errno B <= a0 < as_errno B + 4 -> in_img segs a0) ->
  forall I : YStrtodRowX.strtod_img,
  (forall fx1, YStrtodRowX.astrtod_realizes_x (fx := fx1) segs B ARx I (pa_sigma AS_strtod) STK_RT_STRTOD
     strtod_c.strtod_model ev_txt_ok) ->
  ev_strtod_site I ->
  (forall fx1, aintrin_realizes_xm (fx := fx1) segs B ARx OCpy (pa_sigma AS___asan_memcpy)) ->
  forall a, KR a -> KS a.
Definition ev_D_stmt : Prop := ev_img_ok -> forall a, KT a -> KC a -> KR a.
Definition ev_E_stmt : Prop :=
  ev_img_ok ->
  (forall fx1, astrcmp_realizes_xrom (fx := fx1) segs B ARx pa_relro_lo pa_relro_hi (pa_sigma AS___wrap_strcmp)) ->
  (forall fx1, abcmp_realizes_xm (fx := fx1) segs B ARx (pa_sigma AS___wrap_bcmp)) ->
  forall a, KD a -> KC a.
Definition ev_F_stmt : Prop := ev_img_ok -> forall a, KT a -> KD a.
(* T: the tail to the exit; the exit is ev_to_exit itself *)
Definition ev_T_stmt : Prop := ev_img_ok -> forall a, KT a.
End c.
