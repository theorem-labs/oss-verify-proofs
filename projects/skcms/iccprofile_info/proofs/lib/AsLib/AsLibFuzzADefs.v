(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Asan.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec FuzzContract.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsSpec AsLibWP1Spec AsLibTagsLib AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec AsLibKit AsLibPlace.
Import ListNotations.
Open Scope bv_scope.
Import ASX. Import ASXS.
Ltac Zify.zify_post_hook ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Unset Lia Cache. Unset Nia Cache.   (* [comment removed for export] *)
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].

#[local] Abbreviation SEGS := Asan.M.loaded_segments.
#[local] Abbreviation TP := 0x5d9b70%Z.
#[local] Abbreviation GF := 0x5d9240%Z.
#[local] Abbreviation DEPTH := 3584%Z.

(* [comment removed for export] *)
Ltac in_lit := cbn; repeat (first [left; reflexivity | right]).

(* [comment removed for export] *)
Lemma realign160 : forall sp : word, (bv_unsigned sp mod 16 = 0)%Z -> (176 <= bv_unsigned sp)%Z ->
  let u := bv_unsigned (alu64 ALU_AND (alu64 ALU_ADD sp (Z_to_bv 64 (-160))) (Z_to_bv 64 (-32))) in
  (u mod 32 = 0)%Z /\ (bv_unsigned sp - 176 <= u <= bv_unsigned sp - 160)%Z.
Proof.
  intros sp Hal Hge. cbv zeta. pose proof (u64_range sp).
  rewrite u_and64, u_add64, !u_lit64. unfold two64.
  change ((-32) mod 2 ^ 64)%Z with (2 ^ 64 - 2 ^ 5)%Z.
  Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations.
  rewrite land_highmask by lia. lia.
  Ltac Zify.zify_post_hook ::= idtac.
Qed.

(* [comment removed for export] *)
Lemma gfool_apart :
  (forall a v, In (a, v) (aa_c64 asan_abi) -> (a + 8 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a v, In (a, v) (aa_c32 asan_abi) -> (a + 4 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a v, In (a, v) (aa_c8 asan_abi) -> (a + 1 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a, In a (aa_r64 asan_abi) -> (a + 8 <= GF \/ GF + 4 <= a)%Z) /\
  (forall a v, In (a, v) (aa_shb asan_abi) -> (a + 1 <= GF \/ GF + 4 <= a)%Z) /\
  (forall lo hi, In (lo, hi) (aa_ro asan_abi) -> (hi <= GF \/ GF + 4 <= lo)%Z).
Proof.
  cbn -[Z.le Z.add].
  repeat split; intros;
  repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] | H : False |- _ => destruct H end;
  try match goal with H : (_, _) = (_, _) |- _ => injection H as <- <- end; try subst; cbn; lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition parse_pre0 (ceil : Z) (sp prio P : word) (fs : Z) (ch : chain)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let p := bv_unsigned P in
  let q := bv_unsigned prio in
  let s := bv_unsigned sp in
  getr regs 2 = sp /\ getr regs 11 = Z_to_bv 64 0 /\
  getr regs 12 = prio /\ getr regs 13 = Z_to_bv 64 2 /\ getr regs 14 = P /\ getr regs 4 = Z_to_bv 64 (aa_tp asan_abi) /\
  cell32 SEGS mem q 0 /\ cell32 SEGS mem (q + 4) 1 /\ (q mod 8 = 0)%Z /\ heapish ceil q 8 /\ shz mem q 1 /\
  (fs + FS_FRAMES5 <= q)%Z /\ (q + 8 <= fs + FS_SIZE)%Z /\ (q + 8 <= p \/ p + 976 <= q)%Z /\
  writable SEGS mem p 976 /\ (p mod 64 = 0)%Z /\ heapish ceil p 976 /\ shz mem p 122 /\
  (fs + FS_FRAMES5 <= p)%Z /\ (p + 976 <= fs + FS_SIZE)%Z /\
  as_frame SEGS ceil mem sp PARSE_D /\ shz mem (s - PARSE_D) (PARSE_D / 8) /\
  as_env SEGS ceil asan_abi fs ch mem /\ fs_hdr SEGS ceil asan_abi fs mem /\ fs_writable SEGS fs mem /\
  (exists h, acellw SEGS mem (fs + FS_HINT0) h) /\ fs_flags0_but fs [] mem.
Definition parse0_contract (ceil : Z) : Prop :=
  forall sp prio P fs ch (FPI : FPState) regs mem rom ret,
    getr regs 1 = ret -> ret_ok ret -> parse_pre0 ceil sp prio P fs ch FPI regs mem ->
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x81950) mem rom) (mkst (FP:=FPI') regs' ret mem' rom) /\
      regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
      parse_post_as SEGS (Z_to_bv 64 (fs + FS_SIZE)) 0 [] sp prio P fs ch regs mem FPI' regs' mem'.

Section FENVDef.
  Variable ceil : Z.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data : word) (n : Z) (bs : list byte) (fs : Z) (h0 h5 ctx thr t48 t56 dtls v24 : word).
  Record FENV : Prop := MkFENV {
    Hra : getr regs 1 = ret;
    Hret : ret_ok ret;
    Hsp : getr regs 2 = sp;
    Htp : getr regs 4 = Z_to_bv 64 TP;
    Ha0 : getr regs 10 = data;
    Ha1 : getr regs 11 = Z_to_bv 64 n;
    Hn : (0 <= n < 2 ^ 26)%Z;
    Hbs : Z.of_nat (length bs) = n;
    Hal : (bv_unsigned sp mod 16 = 0)%Z;
    Hdal : (bv_unsigned data mod 16 = 0)%Z;
    Hclo : (AS_STKLO <= ceil)%Z;
    Hsplo : (ceil <= bv_unsigned sp - DEPTH)%Z;
    Hsphi : (bv_unsigned sp < 2 ^ 47)%Z;
    Hdpl : ((0 < n)%Z -> appm (bv_unsigned data) n /\ (bv_unsigned data + n <= ceil /\ (bv_unsigned data + n <= fs \/ fs + FS_SIZE <= bv_unsigned data))%Z);
    Hfslo : appm fs FS_SIZE;
    Hfshi : (fs + FS_SIZE <= ceil)%Z;
    Hfsal : (fs mod 4096 = 0)%Z;
    Hblob : forall i, (0 <= i < n)%Z -> mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0));
    Hshd : ashdata mem (bv_unsigned data) n;
    Hstw : awritable SEGS mem (bv_unsigned sp - DEPTH) DEPTH;
    Hstseg : forall i, (bv_unsigned sp - DEPTH <= i < bv_unsigned sp)%Z -> Forall (fun seg => (i < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= i)%Z) SEGS;
    Hstsh : azero mem (AS_SB + (bv_unsigned sp - DEPTH) / 8) (DEPTH / 8);
    Hgfw : awritable SEGS mem GF 4;
    Hgfr : areadable SEGS mem GF 4;
    Hro : forall lo hi i, In (lo, hi) (aa_ro asan_abi) -> (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None;
    Hc64 : forall a v, In (a, v) (aa_c64 asan_abi) -> acell SEGS mem a 8 v;
    Hc32 : forall a v, In (a, v) (aa_c32 asan_abi) -> acell SEGS mem a 4 v;
    Hc8 : forall a v, In (a, v) (aa_c8 asan_abi) -> acell SEGS mem a 1 v;
    Hr64 : forall a, In a (aa_r64 asan_abi) -> areadable SEGS mem a 8;
    Hshb : forall a v, In (a, v) (aa_shb asan_abi) -> mem (Z_to_bv 64 a) = Some (Z_to_bv 8 v);
    Htsd : acellw SEGS mem (aa_tsdv asan_abi) ctx;
    Hctxok : heap_cell_ok ceil (bv_unsigned ctx + 152) fs;
    Hctx : acellw SEGS mem (bv_unsigned ctx + 152) thr;
    Ht48ok : heap_cell_ok ceil (bv_unsigned thr + 48) fs;
    Ht56ok : heap_cell_ok ceil (bv_unsigned thr + 56) fs;
    Ht48 : acellw SEGS mem (bv_unsigned thr + 48) t48;
    Ht56 : acellw SEGS mem (bv_unsigned thr + 56) t56;
    Hdtls : acellw SEGS mem (TP + 0x8) dtls;
    Hdtlsnz : (0 < bv_unsigned dtls < 2 ^ 64 - 1)%Z;
    Hv24ok : heap_cell_ok ceil (bv_unsigned dtls + 24) fs;
    Hv24 : acellw SEGS mem (bv_unsigned dtls + 24) v24;
    Hv24nz : (bv_unsigned v24 <> 0)%Z;
    Hfscell : acell SEGS mem (TP + 0) 8 fs;
    Hh0 : acellw SEGS mem (fs + FS_HINT0) h0;
    Hh5 : acellw SEGS mem (fs + FS_HINT5) h5;
    Hssl : acell SEGS mem (fs + FS_SSL) 8 20;
    Hngc : acell SEGS mem (fs + FS_NEEDSGC) 1 0;
    Hfl0 : azero mem (fs + FS_FLAGS0) FS_FLAGS0_LEN;
    Hfl5 : azero mem (fs + FS_FLAGS5) FS_FLAGS5_LEN;
    Hwh0 : awritable SEGS mem (fs + FS_HINT0) 8;
    Hwh5 : awritable SEGS mem (fs + FS_HINT5) 8;
    Hwfl0 : awritable SEGS mem (fs + FS_FLAGS0) FS_FLAGS0_LEN;
    Hwfl5 : awritable SEGS mem (fs + FS_FLAGS5) FS_FLAGS5_LEN;
    Hwfr0 : awritable SEGS mem (fs + FS_FRAMES0) FS_FRAMES_LEN;
    Hwfr5 : awritable SEGS mem (fs + FS_FRAMES5) FS_FRAMES_LEN;
    Hwsf0 : awritable SEGS mem (AS_SB + (fs + FS_FRAMES0) / 8) FS_SHFRAMES_LEN;
    Hwsf5 : awritable SEGS mem (AS_SB + (fs + FS_FRAMES5) / 8) FS_SHFRAMES_LEN }.
End FENVDef.

Arguments Hra {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hret {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hsp {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Htp {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Ha0 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Ha1 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hn {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hbs {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hal {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hdal {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hclo {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hsplo {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hsphi {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hdpl {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hfslo {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hfshi {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hfsal {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hblob {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hshd {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hstw {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hstseg {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hstsh {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hgfw {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hgfr {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hro {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hc64 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hc32 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hc8 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hr64 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hshb {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Htsd {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hctxok {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hctx {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Ht48ok {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Ht56ok {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Ht48 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Ht56 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hdtls {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hdtlsnz {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hv24ok {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hv24 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hv24nz {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hfscell {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hh0 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hh5 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hssl {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hngc {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hfl0 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hfl5 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hwh0 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hwh5 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hwfl0 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hwfl5 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hwfr0 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hwfr5 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hwsf0 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
Arguments Hwsf5 {ceil regs mem ret sp data n bs fs h0 h5 ctx thr t48 t56 dtls v24} _.
