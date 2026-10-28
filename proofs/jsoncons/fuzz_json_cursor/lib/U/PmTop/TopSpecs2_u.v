(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_cursor.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_cursor.lib.U Require Import PmLibDefs_u PmLibSpecs_u PmLayout_u.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module TPS2.
Import PML.
Section Specs.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.

Definition island_W : list L5.range := map (fun iv => (fst iv, snd iv - fst iv)) ll_prist_csrc.

Definition island_post (M' : mem) : Prop :=
  u8 M' 0xd5230 1 /\ u64 M' 0xd5228 CLASSIC_IMP /\ errcat_guard M' 0 /\ convcat_guard M' 0 /\ atexit_cells M' [] /\ u8 M' 0xd5030 0 /\ u8 M' 0xd5031 0 /\ libc_quiet M'.

Definition IOSBI_SCR : Z := 16 + 32.
Definition iosb_init_later_spec : Prop :=
  forall (B rb sp r : Z),
    cps_pure PC_IOSB_INIT r sp IOSBI_SCR [(B, 136)]
      (fun R M => entry L R M sp r IOSBI_SCR /\ a0 R B /\ a1 R rb /\ 1 <= rb < 2 ^ 47 /\ PMS.gloc_done M /\ img_ro M /\ obj_on_stack L sp B 152 /\ L5.defined M B 152)
      (fun R M R' M' => iosb_at M' B 0 rb).
Definition iosb_init_first_spec : Prop :=
  forall (B rb sp r : Z),
    cps_pure PC_IOSB_INIT r sp (16 + PMS.ISLAND_SCR) ((B, 136) :: island_W)
      (fun R M => entry L R M sp r (16 + PMS.ISLAND_SCR) /\ a0 R B /\ a1 R rb /\ 1 <= rb < 2 ^ 47 /\ ls_ok LS0 M /\ obj_on_stack L sp B 152 /\ L5.defined M B 152)
      (fun R M R' M' => iosb_at M' B 0 rb /\ island_post M').

Definition sbuf_at (M : mem) (SB : Z) (rep : srep) : Prop :=
  let D := srep_data (SB + 64) rep in let n := Z.of_nat (length (srep_chars rep)) in
  u64 M SB VT_STRINGBUF /\ u64 M (SB + 8) CLASSIC_IMP /\ u64 M (SB + 16) D /\ u64 M (SB + 24) D /\ u64 M (SB + 32) (D + n) /\
  u64 M (SB + 40) 0 /\ u64 M (SB + 48) 0 /\ u64 M (SB + 56) 0 /\ str_at M (SB + 64) rep /\ u64 M (SB + 88) (D + n) /\ u32 M (SB + 96) 8.
End Specs.
Section SpecsH.
Context {SCFG_P : ScfgP}.
Variable L : heap_layout.
Variable HI : heap_iface.
Definition SBUF_SCR : Z := 64 + 48 + PMS.OPNEW_SCR.
Definition sbuf_ctor_spec : Prop :=
  forall (LB : list (Z * Z)) (cr : credit) (SB so sp r : Z) (srep0 : srep),
    cps_heap L HI PC_SBUF_CTOR r sp SBUF_SCR LB cr
      (fun R M => entry L R M sp r SBUF_SCR /\ a0 R SB /\ a1 R so /\ a2 R 8 /\
                  str_at_w M so srep0 /\ (forall b, In b (srep_blocks srep0) -> In b LB) /\ Z.of_nat (length (srep_chars srep0)) < 2 ^ 26 /\
                  obj_on_stack L sp SB 104 /\ obj_on_stack L sp so 24 /\ apart SB 104 so 24 /\ L5.defined M SB 104 /\ L5.defined M so 24   /\ PMS.gloc_done M /\ img_ro M /\
                  credit_ok L cr (copy_cap (Z.of_nat (length (srep_chars srep0)))))
      (fun R M R' M' LB' cr' LBk W => exists rep,
          srep_chars rep = srep_chars srep0 /\ sbuf_at M' SB rep /\
          LB' = srep_blocks rep ++ LB /\ LBk = LB /\
          (forall b, In b (srep_blocks rep) -> L5C.fresh_block L LB M' (fst b) (snd b) /\ snd b = copy_cap (Z.of_nat (length (srep_chars srep0))) /\ cr' = debit L cr (snd b)) /\
          (srep_blocks rep = [] -> cr' = cr) /\
          W = [(SB, 104)]).
End SpecsH.
End TPS2.
