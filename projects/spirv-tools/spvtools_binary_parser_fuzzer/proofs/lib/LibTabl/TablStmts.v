(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_TablStmts () := "C46Stdlib5Lists4List2hdC59OSSVerify5KrLib6LibPrs:PrsGrammar4sx32C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01I47Corelib7Numbers7BinNums1Z00".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition sx32 (x : Z) : Z := if x <? 2 ^ 31 then x else x + 2 ^ 64 - 2 ^ 32.

Lemma sx32_prs : forall x, sx32 x = PrsGrammar.sx32 x.
Proof.
ltac2:(KReplay.run1 (kr_t_TablStmts ()) [] "h01xp;1p;2p-1p10000p4p710p8g000Gj11Tg001Bj20Tg001\R0f0#1,00W0o"). Qed.

Section TablStmts.
Context {AC : AllocCeiling}.
Variable SEGS : list Segment.
Variable L : Layout.
Variable MI : MallocIface SEGS L.
Variable ST : StaticsIface SEGS L.

#[local] Notation cfg fx R pc M model :=
  (mkCfg (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) model).
#[local] Abbreviation vec32 := (CRep.vec32 MI).
#[local] Abbreviation callB := (LibEff.callB MI ST).
#[local] Abbreviation retB := (LibEff.retB MI ST).
#[local] Abbreviation roomL := (LibEff.roomL MI).
#[local] Abbreviation fld := (CRep.fld SEGS).
#[local] Abbreviation NEW_STACK := (ContStmts.NEW_STACK SEGS L MI).
#[local] Abbreviation ro_span := (PrsGrammar.ro_span SEGS L).
#[local] Abbreviation ro_cstr := (PrsGrammar.ro_cstr SEGS L).
#[local] Abbreviation leafA := (PrsGrammar.leafA SEGS L).

Variable G : grammar.
Variable tc : tabl_consts.

Variable idesc : Z -> Z -> Prop.
Variable odesc : Z -> Z -> Z -> Prop.
Variable edesc : Z -> Z -> Z -> Prop.

Definition fixword_stmt : Prop :=
  leafA (tc_fixword tc)
        (fun R _ => exists w e, 0 <= w < 2 ^ 32 /\ getr R 10%bv = Z_to_bv 64 (sx32 w)
                               /\ 0 <= e < 2 ^ 32 /\ getr R 11%bv = Z_to_bv 64 e)
        (fun _ R' => exists r, 0 <= r < 2 ^ 32 /\ getr R' 10%bv = Z_to_bv 64 (sx32 r)).

Definition is_host_endian_stmt : Prop :=
  leafA (tc_is_host_endian tc) (fun R _ => exists x, 0 <= x < 2 ^ 32 /\ getr R 10%bv = Z_to_bv 64 x)
        (fun _ R' => exists r, (r = 0 \/ r = 1) /\ getr R' 10%bv = Z_to_bv 64 r).

Definition bool_leaf (pc : Z) : Prop :=
  leafA pc (fun R _ => exists x, 0 <= x < 2 ^ 32 /\ getr R 10%bv = Z_to_bv 64 x)
        (fun _ R' => exists b : bool, getr R' 10%bv = Z_to_bv 64 (if b then 1 else 0)).

Definition generates_type_stmt (gt : Z -> bool) : Prop :=
  leafA (tc_generates_type tc) (fun R _ => exists x, 0 <= x < 2 ^ 32 /\ getr R 10%bv = Z_to_bv 64 x)
        (fun R R' => exists b : bool, getr R' 10%bv = Z_to_bv 64 (if b then 1 else 0)
                               /\ (b = true -> exists x, 0 <= x < 2 ^ 32 /\ getr R 10%bv = Z_to_bv 64 x /\ gt x = true)).
Definition is_ext_inst_stmt : Prop := bool_leaf (tc_is_ext_inst tc).

Definition is_optional_stmt : Prop :=
  leafA (tc_is_optional tc) (fun R _ => exists x, 0 <= x < 2 ^ 32 /\ getr R 10%bv = Z_to_bv 64 x)
        (fun R R' => exists b : bool, getr R' 10%bv = Z_to_bv 64 (if b then 1 else 0)
                               /\ (b = true -> exists x, 42 <= x < 2 ^ 32 /\ getr R 10%bv = Z_to_bv 64 x)).
Definition is_nonsemantic_stmt : Prop := bool_leaf (tc_is_nonsemantic tc).

Definition fpenc_stmt : Prop :=
  leafA (tc_fpenc tc) (fun _ _ => True) (fun _ R' => exists r, 0 <= r < 2 ^ 32 /\ getr R' 10%bv = Z_to_bv 64 r).

Definition operand_type_str_stmt : Prop :=
  leafA (tc_operand_type_str tc) (fun R _ => exists x, 0 <= x < 2 ^ 32 /\ getr R 10%bv = Z_to_bv 64 x)
        (fun _ R' => exists p n, ro_cstr p n /\ n <= 256 /\ getr R' 10%bv = Z_to_bv 64 p).

Definition idesc_name_stmt : Prop :=
  leafA (tc_idesc_name tc) (fun R _ => exists d op, idesc d op /\ getr R 10%bv = Z_to_bv 64 d)
        (fun _ R' => exists p n, ro_cstr p n /\ n <= 256 /\ getr R' 10%bv = Z_to_bv 64 p).

Definition idesc_operands_stmt : Prop :=
  leafA (tc_idesc_operands tc) (fun R _ => exists d op, idesc d op /\ getr R 10%bv = Z_to_bv 64 d)
        (fun R R' => forall d op, idesc d op -> getr R 10%bv = Z_to_bv 64 d ->
           exists p l, g_op G op = Some l /\ ro_span p l /\ p mod 4 = 0 /\
                       getr R' 10%bv = Z_to_bv 64 p /\ getr R' 11%bv = Z_to_bv 64 (Zlen l)).
Definition odesc_operands_stmt : Prop :=
  leafA (tc_odesc_operands tc) (fun R _ => exists d t v, odesc d t v /\ getr R 10%bv = Z_to_bv 64 d)
        (fun R R' => forall d t v, odesc d t v -> getr R 10%bv = Z_to_bv 64 d ->
           exists p l, g_operand G t v = Some l /\ ro_span p l /\ p mod 4 = 0 /\
                       getr R' 10%bv = Z_to_bv 64 p /\ getr R' 11%bv = Z_to_bv 64 (Zlen l)).
Definition edesc_operands_stmt : Prop :=
  leafA (tc_edesc_operands tc) (fun R _ => exists d e v, edesc d e v /\ getr R 10%bv = Z_to_bv 64 d)
        (fun R R' => forall d e v, edesc d e v -> getr R 10%bv = Z_to_bv 64 d ->
           exists p l, g_ext G e v = Some l /\ ro_span p l /\ p mod 4 = 0 /\
                       getr R' 10%bv = Z_to_bv 64 p /\ getr R' 11%bv = Z_to_bv 64 (Zlen l)).

Definition odesc_value_stmt : Prop :=
  forall d t v M, odesc d t v -> ro_clear L M -> fld M d 4 v /\ 0x10000 <= d /\ d + 4 <= 2 ^ 47.

Definition strlen_ro_stmt : Prop :=
  leafA (tc_strlen tc) (fun R _ => exists p n, ro_cstr p n /\ getr R 10%bv = Z_to_bv 64 p)
        (fun R R' => forall p n, ro_cstr p n -> getr R 10%bv = Z_to_bv 64 p -> getr R' 10%bv = Z_to_bv 64 n).

Definition opcode_split_stmt : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (w pwc pop : Z) (ret : word),
    getr R 10%bv = Z_to_bv 64 (sx32 w) -> getr R 11%bv = Z_to_bv 64 pwc -> getr R 12%bv = Z_to_bv 64 pop ->
    0 <= w < 2 ^ 32 -> alloc_ceiling <= pwc -> pwc + 2 <= 2 ^ 47 -> alloc_ceiling <= pop -> pop + 2 <= 2 ^ 47 ->
    pwc mod 2 = 0 -> pop mod 2 = 0 ->
    mdef M pwc 2 -> mdef M pop 2 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R',
      msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_opcode_split tc)) M (seg_rom SEGS))
                  (@mkst fx R' ret (wbytes (wbytes M (Z_to_bv 64 pwc) (word_to_le_bytes 2 (Z_to_bv 64 (w / 2 ^ 16))))
                                          (Z_to_bv 64 pop) (word_to_le_bytes 2 (Z_to_bv 64 (w mod 2 ^ 16)))) (seg_rom SEGS))
      /\ kept R R'.

Definition binary_endianness_stmt : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (pb pe words n sp : Z) (ret : word),
    ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 pb -> getr R 11%bv = Z_to_bv 64 pe -> getr R 2%bv = Z_to_bv 64 sp ->
    fld M pb 8 words -> fld M (pb + 8) 8 n -> 1 <= n -> 0 < words -> words + 4 * n <= 2 ^ 47 -> mdef M words 4 ->
    alloc_ceiling <= pe -> pe + 4 <= 2 ^ 47 -> mdef M pe 4 -> alloc_ceiling <= pb -> pb + 16 <= 2 ^ 47 ->
    pb mod 8 = 0 -> words mod 4 = 0 -> pe mod 4 = 0 ->
    (forall a, zwin (sp - tc_lookup_stack tc) sp a -> ~ zwin pe (pe + 4) a /\ ~ zwin pb (pb + 16) a) ->
    stack_room SEGS M sp (tc_lookup_stack tc) -> alloc_ceiling <= sp - tc_lookup_stack tc -> sp < 2 ^ 47 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M' (r e : Z),
      msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_binary_endianness tc)) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31 /\ 0 <= e < 2 ^ 32
      /\ fld M' pe 4 e /\ (r = 0 -> 0 <= e < 2)
      /\ frame_eq (fun a => zwin pe (pe + 4) a \/ zwin (sp - tc_lookup_stack tc) sp a) M M'
      /\ (forall a : word, M a <> None -> M' a <> None).

Definition lookup_shape (pc : Z) (nargs : nat) (found : Z -> Z -> Prop) (hnd : Z -> Z -> Z -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (x y pd sp : Z) (ret : word),
    ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 x -> 0 <= x < 2 ^ 32 ->
    (nargs = 2%nat -> getr R 11%bv = Z_to_bv 64 pd) ->
    (nargs = 3%nat -> getr R 11%bv = Z_to_bv 64 (sx32 y) /\ 0 <= y < 2 ^ 32 /\ getr R 12%bv = Z_to_bv 64 pd) ->
    getr R 2%bv = Z_to_bv 64 sp ->
    alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 -> mdef M pd 8 -> pd mod 8 = 0 ->
    (forall a, zwin (sp - tc_lookup_stack tc) sp a -> ~ zwin pd (pd + 8) a) ->
    stack_room SEGS M sp (tc_lookup_stack tc) -> alloc_ceiling <= sp - tc_lookup_stack tc -> sp < 2 ^ 47 -> sp mod 16 = 0 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M' (r d : Z),
      msteps SEGS (@mkst fx R (Z_to_bv 64 pc) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31
      /\ fld M' pd 8 d
      /\ (r = 0 <-> found x y) /\ (r = 0 -> hnd d x y)
      /\ frame_eq (fun a => zwin pd (pd + 8) a \/ zwin (sp - tc_lookup_stack tc) sp a) M M'
      /\ (forall a : word, M a <> None -> M' a <> None).

Definition lookup_opcode_stmt : Prop :=
  lookup_shape (tc_lookup_opcode tc) 2 (fun op _ => exists l, g_op G op = Some l) (fun d op _ => idesc d op).
Definition lookup_operand_stmt : Prop :=
  lookup_shape (tc_lookup_operand tc) 3 (fun t v => exists l, g_operand G t v = Some l) (fun d t v => odesc d t v).
Definition lookup_ext_stmt : Prop :=
  lookup_shape (tc_lookup_ext tc) 3 (fun e v => exists l, g_ext G e v = Some l) (fun d e v => edesc d e v).

Definition spec_lookup_stmt : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (this op sp : Z) (ret : word),
    ro_clear L M -> img_ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 this -> getr R 11%bv = Z_to_bv 64 op -> 0 <= op < 2 ^ 31 ->
    getr R 2%bv = Z_to_bv 64 sp ->
    stack_room SEGS M sp (tc_lookup_stack tc) -> alloc_ceiling <= sp - tc_lookup_stack tc -> sp < 2 ^ 47 -> sp mod 16 = 0 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M' (r : Z),
      msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_spec_lookup tc)) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31 /\ (r = 0 <-> g_specop G op = true)
      /\ frame_eq (fun a => zwin (sp - tc_lookup_stack tc) sp a) M M'
      /\ (forall a : word, M a <> None -> M' a <> None).

Definition import_type_get_stmt : Prop :=
  forall (fx : FPState) (A : AS MI) (R : bvmap 5 word) (M : mem) (model : Model) (p n sp : Z) (ret : word),
    ainv MI A M model -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 p -> getr R 2%bv = Z_to_bv 64 sp ->
    0 < p -> p + n + 1 <= 2 ^ 47 -> 0 <= n -> mdef M p (n + 1) ->
    (forall i, 0 <= i < n -> exists c, 0 < c < 256 /\ fld M (p + i) 1 c) -> fld M (p + n) 1 0 ->
    placed MI A p (n + 1) -> (forall a, zwin p (p + n + 1) a -> ~ zwin (sp - tc_import_stack tc) sp a) ->
    stack_room SEGS M sp (tc_import_stack tc) -> alloc_ceiling <= sp - tc_import_stack tc -> sp < 2 ^ 47 -> sp mod 16 = 0 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M' (r : Z),
      msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_import_type_get tc)) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ 0 <= r < 2 ^ 31
      /\ frame_eq (fun a => zwin (sp - tc_import_stack tc) sp a) M M'
      /\ (forall a : word, M a <> None -> M' a <> None).

Definition room_pushes (A : AS MI) (lv : list (Z * Z)) (len cap : Z) (k : nat) : Prop :=
  forall c, cap <= c -> len <= c -> c < len + Z.of_nat k -> roomL A ((0, 4 * c) :: lv) (4 * vgrow c).

Definition junk (A : AS MI) (a : Z) : Prop :=
  0 < a < alloc_ceiling /\ ~ in_ranges (ly_img L) a /\ forall q k, In (q, k) (live MI A) -> ~ (q <= a < q + k).

Definition pushes_post (A A' : AS MI) (len k b cap b' cap' : Z) : Prop :=
  cap <= cap' <= Z.max cap (2 * (len + k)) /\ (cap' = cap -> b' = b /\ live MI A' = live MI A) /\
  (cap' <> cap ->
     (forall q k, In (q, k) (live MI A') <-> (In (q, k) (live MI A) /\ q <> b) \/ (q = b' /\ k = 4 * cap')) /\
     (forall q k, In (q, k) (live MI A) -> q <> b -> q <> b')).

Definition caps_bound (len cap : Z) (k : Z) : Z := 4 * vgrow (Z.max cap (2 * (len + k))).
Definition pushes_fp (A : AS MI) (pat b cap b' cap' : Z) (a : Z) : Prop :=
  zwin pat (pat + 24) a \/ (b <> 0 /\ zwin b (b + 4 * cap) a) \/ zwin b' (b' + 4 * cap') a \/ junk A a.

Definition push_types_stmt (cpb : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret pspan pat b cap p : Z) (xs l : list Z) (K : TSet),
    let STK := tc_pattern_stack tc + (vc_stack cpb + NEW_STACK) in
    callB A s R M model sp ret STK -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 pspan -> getr R 11%bv = Z_to_bv 64 pat ->
    fld M pspan 8 p -> fld M (pspan + 8) 8 (Zlen l) -> ro_span p l -> p mod 4 = 0 -> Zlen l <= g_maxlen G ->
    Forall (fun t => 0 <= t < 2 ^ 31) l ->
    alloc_ceiling <= pspan -> pspan + 16 <= 2 ^ 47 -> (forall a, zwin pspan (pspan + 16) a -> ~ zwin (sp - STK) sp a) ->
    vec32 A M pat b xs cap -> obj_ok MI A sp STK pat 24 -> pat mod 8 = 0 ->
    (forall a, zwin pspan (pspan + 16) a -> ~ zwin pat (pat + 24) a) ->
    caps_bound (Zlen xs) cap (Zlen l) <= NMAX MI ->
    room_pushes A (live MI A) (Zlen xs) cap (length l) ->
    (forall A' R' M' model' (b' cap' : Z),
        retB A' s R R' M' model model' ->
        vec32 A' M' pat b' (push_types l xs) cap' ->
        pushes_post A A' (Zlen xs) (Zlen l) b cap b' cap' ->
        eff MI A A' M M' (sp - STK, sp) (pushes_fp A pat b cap b' cap') ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (tc_push_types tc) M model) K.

Definition take_first_stmt (cpb : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret pat b cap : Z) (xs : list Z) (K : TSet),
    let STK := tc_pattern_stack tc + (vc_stack cpb + NEW_STACK) in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 pat ->
    vec32 A M pat b xs cap -> xs <> [] -> obj_ok MI A sp STK pat 24 -> pat mod 8 = 0 ->
    Forall (fun t => 0 <= t < 2 ^ 31) xs ->
    caps_bound (Zlen xs - 1) cap 3 <= NMAX MI ->
    room_pushes A (live MI A) (Zlen xs - 1) cap 3 ->
    (forall A' R' M' model' (b' cap' : Z),
        retB A' s R R' M' model model' ->
        getr R' 10%bv = Z_to_bv 64 (fst (take_first xs)) ->
        vec32 A' M' pat b' (snd (take_first xs)) cap' ->
        pushes_post A A' (Zlen xs - 1) 3 b cap b' cap' ->
        eff MI A A' M M' (sp - STK, sp) (pushes_fp A pat b cap b' cap') ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (tc_take_first tc) M model) K.

Definition vec32_pbslow_stmt (xb : Z) (c : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret v b cap src x : Z) (xs : list Z) (K : TSet),
    let STK := vc_stack c + NEW_STACK in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 v -> getr R 11%bv = Z_to_bv 64 src ->
    vec32 A M v b xs cap -> Zlen xs = cap -> obj_ok MI A sp STK v 24 -> v mod 8 = 0 ->
    fld M src 4 x -> 0 <= x < xb -> obj_ok MI A sp STK src 4 -> 0 <= src -> src + 4 <= 2 ^ 63 -> src mod 4 = 0 ->
    (forall a, zwin src (src + 4) a -> ~ zwin v (v + 24) a) ->
    4 * vgrow cap <= NMAX MI ->
    roomL A (live MI A) (4 * vgrow cap) ->
    (forall A' R' M' model' (b' : Z),
        retB A' s R R' M' model model' ->
        vec32 A' M' v b' (xs ++ [x]) (vgrow cap) ->
        getr R' 10%bv = Z_to_bv 64 (b' + 4 * (Zlen xs + 1)) ->
        lapply (live MI A) (LAdd b' (4 * vgrow cap) :: del_if b) (live MI A') ->
        eff MI A A' M M' (sp - STK, sp)
            (fun a => zwin v (v + 24) a \/ (b <> 0 /\ zwin b (b + 4 * cap) a) \/ zwin b' (b' + 4 * vgrow cap) a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (vc_entry c) M model) K.

End TablStmts.
