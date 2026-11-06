(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import decidable.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes
  PureModel VmLedger AllocIface AsanCeil AgentLib.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Export
  MallocLayout MallocTree MallocOps MallocShape RefLrSc RefStep RefStmts RefSys RefPieces RefStep3 RefCalloc.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Reloc Require Export RelocKit.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Mallocng Require Export RelocLayout.
Import ListNotations.
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint code_blk_of (chs : list cchunk) (c : Z) : option positive :=
  match chs with
  | [] => None
  | ch :: chs' => if (cc_start ch <=? c) && (c <? cc_start ch + 4 * cc_n ch) then Some (cc_blk ch)
                  else code_blk_of chs' c
  end.

Ltac rl_unfold_pcs e :=
  eval cbv beta iota delta [reloc_layout
    PC_MALLOC PC_FREE PC_CALLOC PC_LIBC_FREE PC_MALLOC_IMPL PC_GET_META PC_NTFREE PC_ALLOC_META PC_ALLOC_SLOT
    PC_ENFRAME PC_ALLZEROP PC_MMAP PC_MPROTECT PC_MUNMAP PC_VM_WAIT PC_SYSCALL_RET PC_ERRNO_LOC PC_LOCK
    PC_UNLOCK PC_MEMCPY PC_MEMSET] in e.

(* [comment removed for export] *)
Ltac rl_name_of e :=
  let e1 := rl_unfold_pcs e in
  lazymatch e1 with
  | (bv_unsigned (rl _ ?c) + ?off)%Z => eval vm_compute in (c + off)%Z
  | (bv_unsigned (rl _ ?c) - ?off)%Z => eval vm_compute in (c - off)%Z
  | bv_unsigned (rl _ ?c) => eval vm_compute in c
  | _ => let _ := match goal with _ => check_closed_term e1 end in eval vm_compute in e1
  end.

(* [comment removed for export] *)
Ltac rl_name_of_pc pc :=
  let p := eval lazy beta iota zeta delta -[rl rl_delta] in pc in
  lazymatch p with
  | rl _ ?c => eval vm_compute in c
  | _ => let _ := match goal with _ => check_closed_term p end in eval vm_compute in (bv_unsigned p)
  end.

(* [comment removed for export] *)
Ltac rl_pc_of J :=
  let b := eval vm_compute in (code_blk_of canon_code J) in
  lazymatch b with
  | Some ?b0 => constr:(rl (rl_delta b0) J)
  | _ => fail "rl_pc_of: not a shared code address:" J
  end.

(* [comment removed for export] *)
Notation "'pc+' base off" :=
  (ltac:(let n := rl_name_of (bv_unsigned base + off)%Z in let p := rl_pc_of n in exact p))
  (at level 10, base constr at level 9, off constr at level 9, only parsing).
Notation "'zpc+' base off" :=
  (ltac:(let n := rl_name_of (bv_unsigned base + off)%Z in let p := rl_pc_of n in exact p))
  (at level 10, base constr at level 9, off constr at level 9, only parsing).

(* [comment removed for export] *)
Ltac rl_pc_expose :=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst _ (rl _ _) _ _) _) _ => idtac
  | |- realizes ?segs (mkCfg (mkst ?R ?pc ?m ?rom) ?md) ?T =>
      let p := eval lazy beta iota zeta delta -[rl rl_delta] in pc in
      lazymatch p with
      | rl _ _ => change (realizes segs (mkCfg (mkst R p m rom) md) T)
      | _ => idtac
      end
  | |- _ => idtac
  end.

(* [comment removed for export] *)
Ltac rl_nf p :=
  lazymatch p with
  | rl ?d ?c => let c' := vm_eval c in constr:(rl d c')
  | v_addi ?q ?e => let q' := rl_nf q in
                    lazymatch q' with rl ?d ?c => let c' := vm_eval (c + e)%Z in constr:(rl d c') end
  | btgt ?q ?e => let q' := rl_nf q in
                  lazymatch q' with rl ?d ?c => let c' := vm_eval (c + e)%Z in constr:(rl d c') end
  | at_ ?q ?e => let q' := rl_nf q in
                 lazymatch q' with rl ?d ?c => let c' := vm_eval (c + e)%Z in constr:(rl d c') end
  end.
Ltac rl_pc_nest p :=
  let p' := rl_nf p in
  tryif constr_eq p p' then idtac
  else replace p with p' by (rewrite ?rl_addi, ?rl_btgt, ?rl_at; reflexivity).

#[export] Ltac norm_pc_state st ::=
  tryif has_evar st then idtac
  else lazymatch st with
       | mkst _ ?p _ _ => first [ rl_pc_s p | rl_pc_nest p | wlit p ]
       | _ => idtac
       end.

#[export] Ltac cur_pc k ::=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ => let u := rl_name_of_pc pc in k u
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[export] Ltac lit_bv t ::=
  match goal with
  | _ => let _ := match goal with _ => check_closed_term t end in
         let T := type of t in
         lazymatch eval cbv in T with
         | bv ?n => let u := eval vm_compute in (bv_unsigned t) in
                    constr:(@BV n u ltac:(vm_compute; exact I))
         end
  | _ => t
  end.

(* [comment removed for export] *)
Ltac rl_site_at c k :=
  let r := eval vm_compute in (site_find canon_sites 0%nat c) in
  lazymatch r with
  | Some (?i, _, _) =>
      let sc := eval hnf in (nth_error canon_sites i) in
      lazymatch sc with
      | Some ?cs =>
          let o := eval vm_compute in (cs_op cs) in
          let sh := eval hnf in (cs_shape cs) in
          lazymatch sh with
          | SH20 ?f => let ins := eval cbv beta in (f (rl_imm20 c)) in k i cs o ins
          | SH12 ?f => let ins := eval cbv beta in (f (rl_imm12 c)) in k i cs o ins
          | SH21 ?f => let ins := eval cbv beta in (f (rl_imm21 c)) in k i cs o ins
          end
      end
  | _ => fail "rl_site_at: no code word and no site at" c
  end.

#[export] Ltac solveF ::=
  lazymatch goal with
  | |- fetch_word ?segs (rl (rl_delta ?b) ?c) = Some ?w =>
      let r := eval vm_compute in (code_find canon_code 0%nat b c) in
      lazymatch r with
      | Some (?i, ?z) =>
          let w0 := constr:(@BV 32 z ltac:(vm_compute; exact I)) in
          let chs := eval hnf in (nth_error canon_code i) in
          lazymatch chs with
          | Some ?ch =>
              unify w w0;
              exact (rl_fetch_at i ch c w0 (@eq_refl _ (Some ch)) ltac:(vm_cast_no_check (@eq_refl bool true)))
          end
      | None =>
          rl_site_at c ltac:(fun i cs o ins => unify w (rl_w o c); exact (rl_site_F i cs eq_refl))
      end
  | |- fetch_word ?segs ?pc = Some ?w =>
      tryif check_closed_term (fetch_word segs pc) then
        (let f := eval vm_compute in (fetch_word segs pc) in
         lazymatch f with Some ?w0 => let wl := lit_bv w0 in unify w wl; vm_refl end)
      else
        (* [comment removed for export] *)
        (let p' := rl_nf pc in
         replace pc with p' by (rewrite ?rl_addi, ?rl_btgt, ?rl_at; reflexivity);
         solveF)
  end.

#[export] Ltac solveD ::=
  lazymatch goal with
  | |- decode_any (rl_w ?o ?c) = ?rhs =>
      rl_site_at c ltac:(fun i cs o' ins => unify rhs (Some (ins, 4%Z)); exact (rl_site_D i cs eq_refl))
  | |- decode_any ?w = ?rhs =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with Some (?i, ?sz) => let il := lit_instr i in unify rhs (Some (il, sz)); vm_refl end
  end.

#[export] Ltac cur_instr tac ::=
  rl_pc_expose;
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst _ (rl (rl_delta ?b) ?c) _ _) _) _ =>
      let r := eval vm_compute in (code_find canon_code 0%nat b c) in
      lazymatch r with
      | Some (_, ?z) =>
          let w := constr:(@BV 32 z ltac:(vm_compute; exact I)) in
          let d := eval vm_compute in (decode_any w) in
          lazymatch d with
          | Some (?i, _) => tac w i
          | _ => fail "cur_instr: no decode at" c
          end
      | None => rl_site_at c ltac:(fun i cs o ins => tac (rl_w o c) ins)
      end
  | |- realizes ?segs (mkCfg (mkst _ ?pc _ _) _) _ =>
      tryif check_closed_term (fetch_word segs pc) then
        (let f := eval vm_compute in (fetch_word segs pc) in
         lazymatch f with
         | Some ?w =>
             let d := eval vm_compute in (decode_any w) in
             lazymatch d with
             | Some (?i, _) => tac w i
             | _ => fail "cur_instr: no decode at" pc
             end
         | _ => fail "cur_instr: no fetch at" pc
         end)
      else first [ progress (rl_pc_nest pc); cur_instr tac
                 | fail 1 "cur_instr: pc is neither closed nor a relocated canonical pc:" pc ]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[export] Ltac pc_tac ::=
  lazymatch goal with
  | |- btgt (rl (rl_delta ?b) ?c) (bv_signed (rl_imm21 ?c)) = ?x =>
      let r := eval vm_compute in (site_find canon_sites 0%nat c) in
      lazymatch r with
      | Some (?i, _, SK_jal ?X ?t) =>
          unify x (rl (rl_delta X) t); exact (rl_site_J i _ X t eq_refl eq_refl)
      end
  | |- v_addi (rl ?d ?c) ?e = ?x =>
      let c' := vm_eval (c + e)%Z in unify x (rl d c'); exact (rl_addi_lit d c e c' eq_refl)
  | |- btgt (rl ?d ?c) ?e = ?x =>
      let c' := vm_eval (c + e)%Z in unify x (rl d c'); exact (rl_btgt_lit d c e c' eq_refl)
  | |- v_jalr (rl ?d ?c) ?e = ?x =>
      let c' := vm_eval (c + e)%Z in
      unify x (rl d c'); refine (rl_jalr_fetch rl_segs d c e c' _ eq_refl _); solveF
  | |- ?l = ?x => let lit := word_lit l in unify x lit; apply bv_eq; vm_compute; reflexivity
  end.

#[export] Ltac addr_tac ::=
  regnorm; imm_norm; rewrite ?v_addi_0;
  first [ reflexivity
        | rl_layout_unfold; rl_norm_s; first [ reflexivity | f_equal; reflexivity ]
        | bveq | f_equal; first [reflexivity | bveq]
        | match goal with |- ?g => fail 100 "addr_tac cannot prove" g end ].

#[export] Ltac mach_jr Hp HS ::=
  eapply rz_step_pc;
  [ mpure Hp
  | eapply step_jalr_x0; [ solveF | reflexivity | solveD | regnorm; imm_norm; klitsg; reflexivity ]
  | lazymatch goal with
    | |- v_jalr (Z_to_bv 64 _) _ = _ => pc_tac
    | |- v_jalr (@BV _ _ _) _ = _ => pc_tac
    | |- v_jalr (rl _ _) _ = _ => pc_tac
    | |- ?g => fail "mach_jr: target not literal:" g
    end
  | ].

(* [comment removed for export] *)
#[export] Ltac mach_assert Hp HS ::=
  let Hb := fresh "Hb" in let EQ := fresh "EQ" in
  destruct (tsafe_assert_inv _ _ _ _ HS) as [Hb EQ];
  rewrite EQ in HS; rewrite EQ; clear EQ; mnorm HS;
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst _ (rl (rl_delta ?b) ?c) _ _) _) _ =>
      let f := eval vm_compute in (match code_find canon_code 0%nat b (c + 4)%Z with Some (_, z) => z | None => 0%Z end) in
      lazymatch f with
      | 35%Z => first [ mach_br_dir Hp HS true ltac:(by_bool Hb) | mach_br_dir Hp HS false ltac:(by_bool Hb) ]
      | _ => first [ mach_br_dir Hp HS false ltac:(by_bool Hb) | mach_br_dir Hp HS true ltac:(by_bool Hb) ]
      end
  end;
  clear Hb.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[export] Ltac call_side Hp Hag HI HW HS ::=
  cbv delta [ALLOC_STACK];
  lazymatch goal with
  | |- md_pure _ => mpure Hp
  | |- ms_vm _ = m_vmmaps _ => symmetry; apply with_vmmaps_vmmaps
  | |- magree _ _ => exact Hag
  | |- minv _ _ => exact HI
  | |- wtop _ => exact (minv_ceil _ _ HI)
  | |- bv_unsigned (getr _ _) = _ => sys_reg
  | |- bytes_le_to_Z ?b = _ =>
      match goal with
      | Hv : bytes_le_to_Z b = bv_unsigned (le_val b), Hc : c_eq (le_val b) _ = true |- _ =>
          rewrite Hv, (c_eq_eq _ _ Hc); vm_compute; reflexivity
      end
  | |- rdn _ _ _ _ = Some _ =>
      first [ assumption
            | eapply (magree_rd _ _ _ _ _ Hag (minv_lo64 _ _ HI)); eassumption ]
  | |- getr _ _ = ?v =>
      regnorm;
      lazymatch goal with |- ?l = ?r =>
        tryif has_evar r then
          (imm_norm;
           lazymatch goal with |- ?l1 = _ =>
             let l' := addi_nf l1 in
             tryif constr_eq l1 l' then reflexivity
             else (transitivity l';
                   [ rewrite ?v_addi_addi'; zsum_norm; rewrite ?v_addi_0;
                     first [reflexivity | klitsg; first [reflexivity | bveq]]
                   | reflexivity ])
           end)
        else (imm_norm; rewrite ?v_addi_addi', ?v_addi_0;
              first [reflexivity | apply v_addi_back; reflexivity
                    | rl_layout_unfold; rl_norm_s; reflexivity
                    | klitsg; first [reflexivity | bveq]])
      end
  | |- _ = negb (c_eq (getr _ _) _) => regnorm; first [ apply nosmall_word | vm_compute; reflexivity | reflexivity ]
  | |- bv_unsigned _ mod 16 = 0 => first [assumption | apply sp_mod16; [assumption | reflexivity | uaddr; alia]]
  | |- ret_ok (rl ?d ?c) => first [assumption | refine (fetch_ret_ok rl_segs (rl d c) _ _); solveF]
  | |- ret_ok _ => first [assumption | apply ret_ok_even; vm_compute; reflexivity]
  | |- wtop _ => exact (minv_ceil _ _ HI)
  | |- tsafe _ _ => first [ exact HS | exact (tsafe_bind_inv _ _ _ HS) ]
  | |- forall a : word, _ -> ?m a <> None => win_nn
  | |- @aslot_at _ _ _ => assumption
  | |- context [alloc_ceiling] => rewrite alloc_ceiling_val; uaddr; alia
  | |- _ => uaddr; alia
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[export] Ltac mrun_until Hp HS Hag HI HW pcZ ::=
  let pcZ := rl_name_of pcZ in
  repeat (cur_pc ltac:(fun u => tryif constr_eq u pcZ then fail else mstep Hp HS Hag HI HW)).

#[export] Ltac mach_join Hp HS Hag HI HW J wl res ::=
  let J := rl_name_of J in
  let Jlit := rl_pc_of J in
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    let CUT := fresh "CUT" in
    lazymatch res with
    | @nil Z =>
      enough (CUT : forall x (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        tsafe (K x s') P ->
        realizes segs (mkCfg (mkst R' Jlit mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (K x s') L))
    | @cons Z ?r1 (@nil Z) =>
      let R1 := constr:(@BV 5 r1 I) in
      enough (CUT : forall x (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        getr R' R1 = x ->
        tsafe (K x s') P ->
        realizes segs (mkCfg (mkst R' Jlit mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (K x s') L))
    | @cons Z ?r1 (@cons Z ?r2 (@nil Z)) =>
      let R1 := constr:(@BV 5 r1 I) in let R2 := constr:(@BV 5 r2 I) in
      enough (CUT : forall x1 x2 (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        getr R' R1 = x1 -> getr R' R2 = x2 ->
        tsafe (K (x1, x2) s') P ->
        realizes segs (mkCfg (mkst R' Jlit mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (K (x1, x2) s') L))
    end;
    [ (* [comment removed for export] *)
      repeat (cur_pc ltac:(fun u => tryif constr_eq u J then fail else mstep Hp HS Hag HI HW));
      [> use_cut CUT res Hag HI HW HS ..]
    | (* [comment removed for export] *)
      join_intro Hag HI HW HS res ]
    end
  end end.

#[export] Ltac mach_join_bool Hp HS Hag HI HW Jt Jf wl XR ::=
  let Jt := rl_name_of Jt in let Jf := rl_name_of Jf in
  let Jtl := rl_pc_of Jt in
  let Jfl := rl_pc_of Jf in
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    let CUT := fresh "CUT" in
    enough (CUT : forall (x : bool) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        XR x R' ->
        tsafe (K x s') P ->
        realizes segs (mkCfg (mkst R' (if x then Jtl else Jfl) mm' rom) (with_vmmaps (ms_vm s') md0))
                 (tshape (K x s') L));
    [ repeat (cur_pc ltac:(fun u => tryif constr_eq u Jt then fail else
                               tryif constr_eq u Jf then fail else mstep Hp HS Hag HI HW));
      [> use_cut_bool CUT Jt Hag HI HW HS ..]
    | join_intro_bool Hag HI HW HS ]
    end
  end end.

(* [comment removed for export] *)
Ltac rl_call_target c imm k :=
  lazymatch imm with
  | rl_imm21 _ =>
      let r := eval vm_compute in (site_find canon_sites 0%nat c) in
      lazymatch r with Some (_, _, SK_jal _ ?t) => k t end
  | _ => let t := eval vm_compute in (c + bv_signed imm)%Z in k t
  end.

#[export] Ltac mstepx Hp HS Hag HI HW HK Hret calls ::=
  cur_instr ltac:(fun w i =>
    let il := lit_instr i in
    lazymatch il with
    | Jal (@BV _ 1 _) ?imm =>
        lazymatch goal with
        | |- realizes _ (mkCfg (mkst _ (rl _ ?c) _ _) _) _ =>
            rl_call_target c imm ltac:(fun t => calls Hp HS Hag HI HW t)
        | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) _ =>
          let t := eval vm_compute in (bv_unsigned (v_addi pc (bv_signed imm))) in
          calls Hp HS Hag HI HW t
        end
    | Jalr (@BV _ 0 _) (@BV _ 1 _) _ => first [ mach_jr Hp HS | mach_ret Hp HS Hag HK HI Hret ]
    | _ => mstep Hp HS Hag HI HW
    end).

#[export] Ltac mrunx_until Hp HS Hag HI HW HK Hret calls pcZ ::=
  let pcZ := rl_name_of pcZ in
  repeat (cur_pc ltac:(fun u => tryif constr_eq u pcZ then fail else mstepx Hp HS Hag HI HW HK Hret calls)).

#[export] Ltac mach_join_k Hp HS Hag HI HW HK Hret calls XTY PCF wl XR ::=
  lazymatch type of HI with minv ?s0 _ =>
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) (with_vmmaps _ ?md0)) (tshape (MallocTree.mbind ?M ?K ?s) ?L) =>
    lazymatch type of HS with tsafe _ ?P =>
    let Kx := fresh "Kx" in
    set (Kx := K) in HS |- *;
    let CUT := fresh "CUT" in
    enough (CUT : forall (x : XTY) (s' : mstate) (mm' : word -> option byte) (R' : bvmap 5 word),
        magree s' mm' -> minv s0 s' ->
        (forall a : word, ms_lo s0 <= bv_unsigned a < ms_hi s0 -> mm' a = mmF a) ->
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) ->
        XR x R' ->
        tsafe (Kx x s') P ->
        realizes segs (mkCfg (mkst R' (PCF x) mm' rom) (with_vmmaps (ms_vm s') md0)) (tshape (Kx x s') L));
    [ repeat (lazymatch goal with
              | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) (tshape (Kx ?x _) _) =>
                  (* [comment removed for export] *)
                  let u := rl_name_of_pc pc in
                  let j := rl_name_of_pc (PCF x) in
                  tryif constr_eq u j then fail else mach Hp HS
              | |- _ => mstepx Hp HS Hag HI HW HK Hret calls
              end);
      [> use_cut_k CUT Kx Hag HI HS ..]
    | join_intro_k Kx Hag HI HW HS ]
    end
  end end.

#[export] Ltac mrun_to_k Hp HS Hag HI HW HK Hret calls Kx PCF ::=
  repeat (lazymatch goal with
          | |- realizes _ (mkCfg (mkst _ ?pc _ _) _) (tshape (Kx ?x _) _) =>
              let u := rl_name_of_pc pc in
              let j := rl_name_of_pc (PCF x) in
              tryif constr_eq u j then fail else mach Hp HS
          | |- _ => mstepx Hp HS Hag HI HW HK Hret calls
          end).

(* [comment removed for export] *)
#[export] Ltac mach_vjoin_core J wl XR CUT ::=
  let J := rl_name_of J in
  let Jlit := rl_pc_of J in
  lazymatch goal with
  | |- realizes ?segs (mkCfg (mkst ?Rf _ ?mmF ?rom) ?mdl) ?T =>
      enough (CUT : forall R' : bvmap 5 word,
        (forall r : reg, wreg wl r = false -> getr R' r = getr Rf r) -> XR R' ->
        realizes segs (mkCfg (mkst R' Jlit mmF rom) mdl) T)
  end.

#[export] Ltac mach_pure Hp HS J ::=
  let J := rl_name_of J in
  repeat (cur_pc ltac:(fun u =>
    tryif constr_eq u J then fail else
    cur_instr ltac:(fun w i =>
      lazymatch i with
      | Branch _ _ _ _ => mach_brc Hp HS
      | _ => mach Hp HS
      end))).

(* [comment removed for export] *)
Ltac rl_names_of l :=
  lazymatch l with
  | @nil Z => constr:(@nil Z)
  | @cons Z ?x ?t => let x' := rl_name_of x in let t' := rl_names_of t in constr:(@cons Z x' t')
  end.

#[export] Ltac mach_pure_l Hp HS stops ::=
  let stops := rl_names_of stops in
  repeat (cur_pc ltac:(fun u =>
    tryif in_zlist u stops then fail else
    cur_instr ltac:(fun w i =>
      lazymatch i with
      | Branch _ _ _ _ => mach_brc Hp HS
      | _ => mach Hp HS
      end))).

#[export] Ltac pc_lit ::=
  lazymatch goal with
  | |- realizes _ (mkCfg (mkst _ (@BV 64 _ _) _ _) _) _ => idtac
  | |- realizes _ (mkCfg (mkst _ (rl _ _) _ _) _) _ => idtac
  | |- realizes _ _ _ => eapply rz_at_pc; [ | symmetry; pc_tac ]
  end.

#[export] Ltac sys_calls Hp HS Hag HI HW t others ::=
  let pmm := rl_name_of (bv_unsigned PC_MMAP) in
  let pmu := rl_name_of (bv_unsigned PC_MUNMAP) in
  let pmp := rl_name_of (bv_unsigned PC_MPROTECT) in
  tryif constr_eq t pmm then
    lazymatch goal with
    | |- realizes _ _ (tshape (MallocTree.mbind (sys_mmap ?k _) _ _) _) =>
        match goal with MM : forall k', mmap_stmt k' |- _ => mach_call Hp HS Hag HI HW (MM k) end
    | |- realizes _ _ (tshape (MallocTree.mbind (sys_mmap_fixed_none _ _) _ _) _) =>
        match goal with MF : mmap_fixed_stmt |- _ => mach_call Hp HS Hag HI HW MF end
    end
  else tryif constr_eq t pmu then
    match goal with MU : munmap_stmt |- _ => mach_call Hp HS Hag HI HW MU end
  else tryif constr_eq t pmp then
    (* [comment removed for export] *)
    mach_pload_new HS; mach_passert HS;
    match goal with MP : mprotect_stmt |- _ => mach_call Hp HS Hag HI HW MP end
  else others t.

(* [comment removed for export] *)
Ltac rl_ret_ok :=
  lazymatch goal with
  | |- ret_ok (rl ?d ?c) => refine (fetch_ret_ok rl_segs (rl d c) _ _); solveF
  | |- ret_ok ?a =>
      let p := eval lazy beta iota zeta delta -[rl rl_delta] in a in
      lazymatch p with
      | rl ?d ?c => change (ret_ok (rl d c)); refine (fetch_ret_ok rl_segs (rl d c) _ _); solveF
      | _ => apply ret_ok_even; vm_compute; reflexivity
      end
  end.

(* [comment removed for export] *)
#[export] Ltac unum ::=
  repeat match goal with
  | |- context [bv_unsigned ?c] =>
      lazymatch c with
      | Z_to_bv _ (bv_unsigned _) => fail
      | _ => check_closed_term c;
             let v := eval vm_compute in (bv_unsigned c) in
             replace (bv_unsigned c) with v by (vm_compute; reflexivity)
      end
  end;
  rl_layout_unfold; rl_bounds; rl_unorm.
