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
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import LibDefs LibFrame LibTagsSpec LibWP2Spec.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsSymCall AsFuzzContract AsLibShadow AsLibDefs AsRtSpec AsLibTagsSpec AsLibWP2Spec AsLibTagsLib AsLibTagsCall AsLibFPLib AsLibParseLib AsLibFrame AsLibEnv AsLibParseSpec AsLibParseDefs AsLibKit AsLibParseF AsLibParseE AsLibParseD AsLibParseC3 AsLibParseC2 AsLibParseC1 AsLibParseB AsLibParseA2 AsLibParseA1 AsLibParseA0 AsLibCurveSpec AsLibPlace.
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

Theorem parse_as_ok : forall ceil,
  imemset976_contract SEGS as_asan ceil -> gettag_contract_as SEGS as_asan ceil -> read_curve_contract_as SEGS as_asan ceil ->
  imemcpy32_contract SEGS as_asan ceil -> xyzd50_contract_as SEGS as_asan ceil ->
  read_a2b_contract_as SEGS as_asan ceil -> read_b2a_contract_as SEGS as_asan ceil ->
  parse_contract_as SEGS as_asan ceil.
Proof.
  intros ceil Hmemset Hgettag Hrc Hmc Hxyz Ha2b Hb2a data len bs sp prio P fs ch FPI regs mem rom ret Hra Hret PRE.
  pose proof PRE as PRE'.
  destruct PRE' as (Hsp & R10 & R11 & R12 & R13 & R14 & Htp & REST).
  assert (HE : PENV ceil regs mem ret sp data prio P len fs bs ch).
  { unfold PENV. cbv zeta. cbn [al_abi as_asan] in Htp, REST.
    split; [exact Hra|]. split; [exact Hret|]. split; [exact Hsp|]. split; [exact Htp|]. exact REST. }
  destruct (blockA_run ceil FPI regs mem rom ret sp data prio P len fs bs ch HE Hmemset Hgettag Hrc Hmc Hxyz Ha2b Hb2a (fun _ => R10) R11 R12 R13 R14)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
  unfold parse_post_as. rewrite BIG_eq. exact Hpost.
Qed.

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

Theorem parse0_ok : forall ceil,
  imemset976_contract SEGS as_asan ceil -> gettag_contract_as SEGS as_asan ceil -> read_curve_contract_as SEGS as_asan ceil ->
  imemcpy32_contract SEGS as_asan ceil -> xyzd50_contract_as SEGS as_asan ceil ->
  read_a2b_contract_as SEGS as_asan ceil -> read_b2a_contract_as SEGS as_asan ceil ->
  forall sp prio P fs ch (FPI : FPState) regs mem rom ret,
    getr regs 1 = ret -> ret_ok ret -> parse_pre0 ceil sp prio P fs ch FPI regs mem ->
    exists (FPI' : FPState) regs' mem',
      msteps SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x81950) mem rom) (mkst (FP:=FPI') regs' ret mem' rom) /\
      regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept (fp_regs (FPState:=FPI)) (fp_regs (FPState:=FPI')) /\
      parse_post_as SEGS (Z_to_bv 64 (fs + FS_SIZE)) 0 [] sp prio P fs ch regs mem FPI' regs' mem'.
Proof.
  intros ceil Hmemset Hgettag Hrc Hmc Hxyz Ha2b Hb2a sp prio P fs ch FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & R11 & R12 & R13 & R14 & Htp & REST).
  pose proof REST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hhdr & _).
  destruct Hhdr as (_ & _ & _ & Hfslo & Hfshi & Hfsal). app_facts.
  (* [comment removed for export] *)
  assert (Hd16 : ((fs + FS_SIZE) mod 16 = 0)%Z).
  { apply mod_add_multiple; [lia | apply (mod_down _ 16 256); [lia | lia | change (16 * 256)%Z with 4096%Z; exact Hfsal] | reflexivity]. }
  assert (Hdap : appm (fs + FS_SIZE) 0%Z).
  { pose proof Hfslo as Hap. unfold appm, AS_LOWEND, AS_HIGHBEG, AS_IMGLO, AS_IMGHI in Hap |- *. unfold FS_SIZE in *. lia. }
  pose proof REST as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hasf & _). destruct Hasf as ((Hsk1 & Hsk2) & _). unfold PARSE_D in Hsk1, Hsk2.
  unfold FS_SIZE in Hfslo, Hfshi, Hd16, Hdap |- *.
  assert (HE : PENV ceil regs mem ret sp (Z_to_bv 64 (fs + 0xb09000)) prio P 0 fs [] ch).
  { unfold PENV, as_data_ok, data_ok, heapish, shdata. cbv zeta. cbn [al_abi as_asan] in Htp, REST. rewrite !u_small by lia.
    split; [exact Hra|]. split; [exact Hret|]. split; [exact Hsp|]. split; [exact Htp|].
    split. { split. { split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. intros i Hi. exfalso. lia. }
             split; [split; [exact Hdap | lia] |]. split; [exact Hd16|].
             split; [apply (mod_down _ 8 2); [lia | lia | exact Hd16]|]. intros g Hg1 Hg2. exfalso.
             Ltac Zify.zify_post_hook ::= Z.div_mod_to_equations. lia. Ltac Zify.zify_post_hook ::= idtac. }
    split; [right; unfold FS_SIZE; lia|]. exact REST. }
  destruct (blockA_run ceil FPI regs mem rom ret sp (Z_to_bv 64 (fs + 0xb09000)) prio P 0 fs [] ch HE Hmemset Hgettag Hrc Hmc Hxyz Ha2b Hb2a
              ltac:(intros; exfalso; lia) R11 R12 R13 R14)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
  unfold parse_post_as. rewrite BIG_eq. exact Hpost.
Qed.
