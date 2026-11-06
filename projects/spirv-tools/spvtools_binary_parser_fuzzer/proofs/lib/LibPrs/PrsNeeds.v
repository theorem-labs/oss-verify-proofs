(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SRealizes RefMemcpyLib LibIface LibBudget LibEff.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Export PrsGrammar.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Section Needs.
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
  leafA (tc_fixword tc) (fun R _ => exists w, 0 <= w < 2 ^ 32 /\ getr R 10%bv = Z_to_bv 64 (sx32 w))
        (fun _ R' => exists r, 0 <= r < 2 ^ 32 /\ getr R' 10%bv = Z_to_bv 64 (sx32 r)).

Definition is_host_endian_stmt : Prop :=
  leafA (tc_is_host_endian tc) (fun _ _ => True)
        (fun _ R' => exists r, (r = 0 \/ r = 1) /\ getr R' 10%bv = Z_to_bv 64 r).

Definition bool_leaf (pc : Z) : Prop :=
  leafA pc (fun R _ => exists x, 0 <= x < 2 ^ 32 /\ getr R 10%bv = Z_to_bv 64 x)
        (fun _ R' => exists b : bool, getr R' 10%bv = Z_to_bv 64 (if b then 1 else 0)).
Variable generates_type : Z -> bool.
Variable is_ext_inst : Z -> bool.
Variable is_nonsemantic : Z -> bool.
Definition generates_type_stmt : Prop := bool_leaf (tc_generates_type tc).
Definition is_ext_inst_stmt : Prop := bool_leaf (tc_is_ext_inst tc).
Definition is_optional_stmt : Prop := bool_leaf (tc_is_optional tc).
Definition is_nonsemantic_stmt : Prop := bool_leaf (tc_is_nonsemantic tc).

Definition fpenc_stmt : Prop :=
  leafA (tc_fpenc tc) (fun _ _ => True) (fun _ R' => exists r, 0 <= r < 2 ^ 32 /\ getr R' 10%bv = Z_to_bv 64 r).

Definition operand_type_str_stmt : Prop :=
  leafA (tc_operand_type_str tc) (fun _ _ => True)
        (fun _ R' => exists p n, ro_cstr p n /\ n <= 256 /\ getr R' 10%bv = Z_to_bv 64 p).

Definition idesc_name_stmt : Prop :=
  leafA (tc_idesc_name tc) (fun R _ => exists d op, idesc d op /\ getr R 10%bv = Z_to_bv 64 d)
        (fun _ R' => exists p n, ro_cstr p n /\ n <= 256 /\ getr R' 10%bv = Z_to_bv 64 p).

Definition idesc_operands_stmt : Prop :=
  leafA (tc_idesc_operands tc) (fun R _ => exists d op, idesc d op /\ getr R 10%bv = Z_to_bv 64 d)
        (fun R R' => forall d op, idesc d op -> getr R 10%bv = Z_to_bv 64 d ->
           exists p l, g_op G op = Some l /\ ro_span p l /\
                       getr R' 10%bv = Z_to_bv 64 p /\ getr R' 11%bv = Z_to_bv 64 (Zlen l)).
Definition odesc_operands_stmt : Prop :=
  leafA (tc_odesc_operands tc) (fun R _ => exists d t v, odesc d t v /\ getr R 10%bv = Z_to_bv 64 d)
        (fun R R' => forall d t v, odesc d t v -> getr R 10%bv = Z_to_bv 64 d ->
           exists p l, g_operand G t v = Some l /\ ro_span p l /\
                       getr R' 10%bv = Z_to_bv 64 p /\ getr R' 11%bv = Z_to_bv 64 (Zlen l)).
Definition edesc_operands_stmt : Prop :=
  leafA (tc_edesc_operands tc) (fun R _ => exists d e v, edesc d e v /\ getr R 10%bv = Z_to_bv 64 d)
        (fun R R' => forall d e v, edesc d e v -> getr R 10%bv = Z_to_bv 64 d ->
           exists p l, g_ext G e v = Some l /\ ro_span p l /\
                       getr R' 10%bv = Z_to_bv 64 p /\ getr R' 11%bv = Z_to_bv 64 (Zlen l)).

Hypothesis odesc_value : forall d t v M, odesc d t v -> ro_clear L M -> fld M d 4 v /\ 0x10000 <= d /\ d + 4 <= 2 ^ 47.

Definition strlen_ro_stmt : Prop :=
  leafA (tc_strlen tc) (fun R _ => exists p n, ro_cstr p n /\ getr R 10%bv = Z_to_bv 64 p)
        (fun R R' => forall p n, ro_cstr p n -> getr R 10%bv = Z_to_bv 64 p -> getr R' 10%bv = Z_to_bv 64 n).

Definition opcode_split_stmt : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (w pwc pop : Z) (ret : word),
    getr R 10%bv = Z_to_bv 64 (sx32 w) -> getr R 11%bv = Z_to_bv 64 pwc -> getr R 12%bv = Z_to_bv 64 pop ->
    0 <= w < 2 ^ 32 -> alloc_ceiling <= pwc -> pwc + 2 <= 2 ^ 47 -> alloc_ceiling <= pop -> pop + 2 <= 2 ^ 47 ->
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
    (forall a, zwin (sp - tc_lookup_stack tc) sp a -> ~ zwin pe (pe + 4) a /\ ~ zwin pb (pb + 16) a) ->
    stack_room SEGS M sp (tc_lookup_stack tc) -> alloc_ceiling <= sp - tc_lookup_stack tc -> sp < 2 ^ 47 ->
    getr R 1%bv = ret -> ret_ok ret ->
    exists R' M' (r e : Z),
      msteps SEGS (@mkst fx R (Z_to_bv 64 (tc_binary_endianness tc)) M (seg_rom SEGS)) (@mkst fx R' ret M' (seg_rom SEGS))
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ - 2 ^ 31 <= r < 2 ^ 31 /\ 0 <= e < 2 ^ 32
      /\ fld M' pe 4 e
      /\ frame_eq (fun a => zwin pe (pe + 4) a \/ zwin (sp - tc_lookup_stack tc) sp a) M M'
      /\ (forall a : word, M a <> None -> M' a <> None).

Definition lookup_shape (pc : Z) (nargs : nat) (found : Z -> Z -> Prop) (hnd : Z -> Z -> Z -> Prop) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : mem) (x y pd sp : Z) (ret : word),
    ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 x -> 0 <= x < 2 ^ 32 ->
    (nargs = 2%nat -> getr R 11%bv = Z_to_bv 64 pd) ->
    (nargs = 3%nat -> getr R 11%bv = Z_to_bv 64 (sx32 y) /\ 0 <= y < 2 ^ 32 /\ getr R 12%bv = Z_to_bv 64 pd) ->
    getr R 2%bv = Z_to_bv 64 sp ->
    alloc_ceiling <= pd -> pd + 8 <= 2 ^ 47 -> mdef M pd 8 ->
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
      /\ kept R R' /\ getr R' 10%bv = Z_to_bv 64 r /\ 0 <= r < 2 ^ 32
      /\ frame_eq (fun a => zwin (sp - tc_import_stack tc) sp a) M M'
      /\ (forall a : word, M a <> None -> M' a <> None).

Fixpoint cap_after (k : nat) (len cap : Z) : Z :=
  match k with
  | O => cap
  | S k' => let cap1 := if len <? cap then cap else vgrow cap in cap_after k' (len + 1) cap1
  end.

Definition room_pushes (A : AS MI) (lv : list (Z * Z)) (len cap : Z) (k : nat) : Prop :=
  forall j, (j < k)%nat -> len + Z.of_nat j = cap_after j len cap ->
    roomL A lv (4 * vgrow (cap_after j len cap)) /\ 4 * vgrow (cap_after j len cap) <= NMAX MI.

Definition junk (A : AS MI) (a : Z) : Prop :=
  0 < a < alloc_ceiling /\ ~ in_ranges (ly_img L) a /\ forall q k, In (q, k) (live MI A) -> ~ (q <= a < q + k).

Definition push_types_stmt (cpb : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret pspan pat b cap p : Z) (xs l : list Z) (K : TSet),
    let STK := tc_pattern_stack tc + (vc_stack cpb + NEW_STACK) in
    callB A s R M model sp ret STK -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 pspan -> getr R 11%bv = Z_to_bv 64 pat ->
    fld M pspan 8 p -> fld M (pspan + 8) 8 (Zlen l) -> ro_span p l -> Zlen l <= g_maxlen G ->
    alloc_ceiling <= pspan -> pspan + 16 <= 2 ^ 47 -> (forall a, zwin pspan (pspan + 16) a -> ~ zwin (sp - STK) sp a) ->
    vec32 A M pat b xs cap -> obj_ok MI A sp STK pat 24 ->
    (forall a, zwin pspan (pspan + 16) a -> ~ zwin pat (pat + 24) a) ->
    4 * (Zlen xs + Zlen l) < NMAX MI ->
    room_pushes A (live MI A) (Zlen xs) cap (length l) ->
    (forall A' R' M' model' (b' cap' : Z),
        retB A' s R R' M' model model' ->
        vec32 A' M' pat b' (push_types l xs) cap' ->
        cap <= cap' /\ (cap' = cap -> b' = b /\ live MI A' = live MI A) /\
        (cap' <> cap -> lapply (live MI A) (LAdd b' (4 * cap') :: del_if b) (live MI A')) ->
        eff MI A A' M M' (sp - STK, sp)
            (fun a => zwin pat (pat + 24) a \/ (b <> 0 /\ zwin b (b + 4 * cap) a) \/ zwin b' (b' + 4 * cap') a
                      \/ junk A a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (tc_push_types tc) M model) K.

Definition take_first_stmt (cpb : vec_consts) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret pat b cap : Z) (xs : list Z) (K : TSet),
    let STK := tc_pattern_stack tc + (vc_stack cpb + NEW_STACK) in
    callB A s R M model sp ret STK ->
    getr R 10%bv = Z_to_bv 64 pat ->
    vec32 A M pat b xs cap -> xs <> [] -> obj_ok MI A sp STK pat 24 ->
    4 * (Zlen xs + 2) < NMAX MI ->
    room_pushes A (live MI A) (Zlen xs - 1) cap 3 ->
    (forall A' R' M' model' (b' cap' : Z),
        retB A' s R R' M' model model' ->
        getr R' 10%bv = Z_to_bv 64 (fst (take_first xs)) ->
        vec32 A' M' pat b' (snd (take_first xs)) cap' ->
        cap <= cap' /\ (cap' = cap -> b' = b /\ live MI A' = live MI A) /\
        (cap' <> cap -> lapply (live MI A) (LAdd b' (4 * cap') :: del_if b) (live MI A')) ->
        eff MI A A' M M' (sp - STK, sp)
            (fun a => zwin pat (pat + 24) a \/ (b <> 0 /\ zwin b (b + 4 * cap) a) \/ zwin b' (b' + 4 * cap') a
                      \/ junk A a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (tc_take_first tc) M model) K.

Record ntfind_consts : Type := NTFIND_CONSTS { nf_entry : Z; nf_miss : Z; nf_hit : Z }.
Variable nfc : ntfind_consts.

Definition nt_find_block_stmt : Prop :=
  forall (fx : FPState) (A : AS MI) (R : bvmap 5 word) (M : mem)
         (this bl bc tid : Z) (ents : list (Z * (Z * (Z * Z * Z)))),
    umapx MI 32 (nval32 SEGS) A M (this + 136) bl bc ents ->
    getr R 10%bv = Z_to_bv 64 this -> getr R 8%bv = Z_to_bv 64 (sx32 tid) -> 0 <= tid < 2 ^ 32 ->
    0 < this -> this + 288 <= 2 ^ 47 ->
    exists R' (pc' : Z),
      msteps SEGS (@mkst fx R (Z_to_bv 64 (nf_entry nfc)) M (seg_rom SEGS)) (@mkst fx R' (Z_to_bv 64 pc') M (seg_rom SEGS))
      /\ (forall r, ~ In r [12; 13; 14; 15; 16; 17]%bv -> getr R' r = getr R r)
      /\ ( pc' = nf_miss nfc
          \/ (pc' = nf_hit nfc /\ exists p v, In (p, (tid, v)) ents /\ getr R' 14%bv = Z_to_bv 64 p)).

Record ds_consts : Type := DS_CONSTS {
  dc_ctor : Z;
  dc_pdiag : Z;
  dc_pdiag_err : Z;
  dc_put_cstr : Z;
  dc_put_u16 : Z; dc_put_u32 : Z; dc_put_u64 : Z; dc_put_int : Z;
  dc_put_string : Z;
  dc_dtor : Z;
  dc_exhausted : Z;
  dc_stack : Z;
  dc_vboff : Z
}.
Variable dc : ds_consts.
Definition DS_SIZE : Z := 392.
Definition DS_MAXBLK : Z := 2 ^ 28.
Definition DS_MAXLEN : Z := 2 ^ 26 + 2 ^ 16.
Definition DS_FL0 : Z := 4098.
Definition DS_FLHEX : Z := 4104.

Variable ds_rep : AS MI -> mem -> Z -> Z -> Z -> list (Z * Z) -> Prop.

Definition sx_cells_hold (M : mem) : Prop := exists s, sx_inv ST s M.

Record ds_rep_laws : Prop := DS_REP_LAWS {
  dl_blocks : forall A M ds err len B, ds_rep A M ds err len B ->
      Zlength B <= 1 /\ (forall q k, In (q, k) B -> In (q, k) (live MI A) /\ 0 < k <= DS_MAXBLK);
  dl_err : forall A M ds err len B, ds_rep A M ds err len B -> fld M (ds + 360) 4 (err mod 2 ^ 32);
  dl_def : forall A M ds err len B, ds_rep A M ds err len B -> mdef M ds DS_SIZE /\ 0 < ds /\ ds + DS_SIZE <= 2 ^ 47 /\ 0 <= len;
  dl_mono : forall A M ds err len len' B, ds_rep A M ds err len B -> len <= len' -> ds_rep A M ds err len' B;

  dl_frame : forall A A' M M' ds err len B, ds_rep A M ds err len B ->
      agree_on (fun a => zwin ds (ds + DS_SIZE) a \/ exists q k, In (q, k) B /\ q <= a < q + k) M M' ->
      (forall blk, In blk B -> In blk (live MI A')) -> ds_rep A' M' ds err len B;

  dl_hex : forall A M ds err len B, ds_rep A M ds err len B ->
      exists vt fl, fld M ds 8 vt /\ (forall M1, img_ro_clear L M1 -> sx_cells_hold M1 -> fld M1 (vt - 24) 8 (dc_vboff dc))
                   /\ 24 <= vt < 2 ^ 47 /\ (fl = DS_FL0 \/ fl = DS_FLHEX)
                   /\ 0 < dc_vboff dc /\ dc_vboff dc + 12 <= 360 /\ fld M (ds + dc_vboff dc + 8) 4 fl /\
      ds_rep A (wbytes M (Z_to_bv 64 (ds + dc_vboff dc + 8)) (word_to_le_bytes 4 (Z_to_bv 64 DS_FLHEX))) ds err len B
}.

Definition ds_foot (ds : Z) (B : list (Z * Z)) (a : Z) : Prop :=
  zwin ds (ds + DS_SIZE) a \/ exists q k, In (q, k) B /\ q <= a < q + k.

Definition blk_xfer (B B' : list (Z * Z)) (lv lv' : list (Z * Z)) : Prop :=
  (forall b, In b B -> In b lv)
  /\ (forall b x, In b B' -> In x lv -> ~ In x B -> fst x <> fst b)
  /\ (forall x, In x lv' <-> In x B' \/ (In x lv /\ ~ In x B)).

Definition ds_room (A : AS MI) : Prop := DS_MAXBLK <= NMAX MI /\ forall n, 0 < n <= DS_MAXBLK -> roomL A (live MI A) n.

Definition ds_room1 (A : AS MI) : Prop :=
  DS_MAXBLK <= NMAX MI /\ forall q n1 n2, 0 < n1 <= DS_MAXBLK -> 0 < n2 <= DS_MAXBLK -> roomL A ((q, n1) :: live MI A) n2.

Definition ds_ctor_stmt : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret ds ppos pcons pstr1 err pstr2 : Z) (K : TSet),
    callB A s R M model sp ret (dc_stack dc) -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 ds -> getr R 11%bv = Z_to_bv 64 ppos -> getr R 12%bv = Z_to_bv 64 pcons ->
    getr R 13%bv = Z_to_bv 64 pstr1 -> getr R 14%bv = Z_to_bv 64 (err mod 2 ^ 64) -> getr R 15%bv = Z_to_bv 64 pstr2 ->
    - 2 ^ 31 <= err < 0 ->
    above_sp MI A sp ds DS_SIZE -> ds mod 8 = 0 -> mdef M ds DS_SIZE ->
    above_sp MI A sp ppos 24 -> mdef M ppos 24 ->
    above_sp MI A sp pstr1 24 -> fld M pstr1 2 0 -> mdef M pstr1 24 -> above_sp MI A sp pstr2 24 -> fld M pstr2 2 0 -> mdef M pstr2 24 ->
    obj_ok MI A sp (dc_stack dc) pcons 48 -> pcons + 48 <= 2 ^ 47 -> fld M (pcons + 32) 8 0 ->
    (forall a, zwin ds (ds + DS_SIZE) a -> ~ zwin ppos (ppos + 24) a /\ ~ zwin pstr1 (pstr1 + 24) a /\ ~ zwin pstr2 (pstr2 + 24) a
                                          /\ ~ zwin pcons (pcons + 48) a) ->
    ds_room A ->
    (forall A' R' M' model' B,
        retB A' s R R' M' model model' ->
        ds_rep A' M' ds err 0 B ->
        blk_xfer [] B (live MI A) (live MI A') ->
        eff MI A A' M M' (sp - dc_stack dc, sp) (ds_foot ds B) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_ctor dc) M model) K.

Definition pdiag_stmt (pc : Z) (with_err : bool) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret ds pcons icount err : Z) (K : TSet),
    callB A s R M model sp ret (dc_stack dc) -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 ds -> getr R 11%bv = Z_to_bv 64 pcons -> getr R 12%bv = Z_to_bv 64 icount ->
    0 <= icount < 2 ^ 63 ->
    (if with_err then getr R 13%bv = Z_to_bv 64 (err mod 2 ^ 64) /\ - 2 ^ 31 <= err < 0 else err = - 4) ->
    above_sp MI A sp ds DS_SIZE -> ds mod 8 = 0 -> mdef M ds DS_SIZE ->
    obj_ok MI A sp (dc_stack dc) pcons 48 -> pcons + 48 <= 2 ^ 47 -> fld M (pcons + 32) 8 0 ->         (forall a, zwin ds (ds + DS_SIZE) a -> ~ zwin pcons (pcons + 48) a) ->
    ds_room A ->
    (forall A' R' M' model' B,
        retB A' s R R' M' model model' ->
        ds_rep A' M' ds err 0 B ->
        blk_xfer [] B (live MI A) (live MI A') ->
        eff MI A A' M M' (sp - dc_stack dc, sp) (ds_foot ds B) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R pc M model) K.
Definition pdiag0_stmt : Prop := pdiag_stmt (dc_pdiag dc) false.
Definition pdiagE_stmt : Prop := pdiag_stmt (dc_pdiag_err dc) true.

Definition ds_op_post (fx : FPState) A (s : SX ST) R M model (sp ret ds err len' : Z) (B : list (Z * Z)) (K : TSet)
           (extra_foot : Z -> Prop) (res_is_ds : bool) : Prop :=
  forall A' R' M' model' B' (J : Z -> Prop),
    retB A' s R R' M' model model' ->
    (res_is_ds = true -> getr R' 10%bv = Z_to_bv 64 ds) ->
    ds_rep A' M' ds err len' B' ->
    blk_xfer B B' (live MI A) (live MI A') ->
    junk_ok MI A J ->
    eff MI A A' M M' (sp - dc_stack dc, sp) (fun a => ds_foot ds B a \/ ds_foot ds B' a \/ J a \/ extra_foot a) ->
    srealizes SEGS (cfg fx R' ret M' model') K.

Definition put_cstr_stmt : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret ds err len p n m : Z) (B : list (Z * Z)) (K : TSet),
    callB A s R M model sp ret (dc_stack dc) -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 ds -> getr R 11%bv = Z_to_bv 64 p -> getr R 12%bv = Z_to_bv 64 m ->
    ds_rep A M ds err len B -> above_sp MI A sp ds DS_SIZE ->
    ro_cstr p n -> 0 <= m <= n ->
    len + m <= DS_MAXLEN ->
    ds_room A ->
    ds_op_post fx A s R M model sp ret ds err (len + m) B K (fun _ => False) true ->
    srealizes SEGS (cfg fx R (dc_put_cstr dc) M model) K.

Definition put_num_stmt (pc : Z) (lo hi : Z) (enc : Z -> Z) : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret ds err len x : Z) (B : list (Z * Z)) (K : TSet),
    callB A s R M model sp ret (dc_stack dc) -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 ds -> getr R 11%bv = Z_to_bv 64 (enc x) -> lo <= x < hi ->
    ds_rep A M ds err len B -> above_sp MI A sp ds DS_SIZE ->
    len + 24 <= DS_MAXLEN ->
    ds_room A ->
    ds_op_post fx A s R M model sp ret ds err (len + 24) B K (fun _ => False) true ->
    srealizes SEGS (cfg fx R pc M model) K.
Definition put_u16_stmt : Prop := put_num_stmt (dc_put_u16 dc) 0 (2 ^ 16) (fun x => x).
Definition put_u32_stmt : Prop := put_num_stmt (dc_put_u32 dc) 0 (2 ^ 32) sx32.
Definition put_u64_stmt : Prop := put_num_stmt (dc_put_u64 dc) 0 (2 ^ 64) (fun x => x).
Definition put_int_stmt : Prop := put_num_stmt (dc_put_int dc) (- 2 ^ 31) (2 ^ 31) (fun x => x mod 2 ^ 64).

Definition put_string_stmt : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret ds err len str : Z) (m : sbuf) (cs : list Z) (B : list (Z * Z)) (K : TSet),
    callB A s R M model sp ret (dc_stack dc) -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 ds -> getr R 11%bv = Z_to_bv 64 str ->
    ds_rep A M ds err len B -> above_sp MI A sp ds DS_SIZE ->
    CRep.str_rep MI A M str m cs -> above_sp MI A sp str 24 ->
    (forall a, zwin ds (ds + DS_SIZE) a -> ~ zwin str (str + 24) a) ->
    (forall b, In b (CRep.str_blocks m) -> ~ In b B) ->
    len + Zlen cs <= DS_MAXLEN ->
    ds_room A ->
    ds_op_post fx A s R M model sp ret ds err (len + Zlen cs) B K (fun _ => False) true ->
    srealizes SEGS (cfg fx R (dc_put_string dc) M model) K.

Definition ds_dtor_stmt : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret ds err len : Z) (B : list (Z * Z)) (K : TSet),
    callB A s R M model sp ret (dc_stack dc) -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 ds ->
    ds_rep A M ds err len B -> above_sp MI A sp ds DS_SIZE ->
    (forall A' R' M' model',
        retB A' s R R' M' model model' ->
        blk_xfer B [] (live MI A) (live MI A') -> mdef M' ds DS_SIZE ->
        eff MI A A' M M' (sp - dc_stack dc, sp) (ds_foot ds B) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_dtor dc) M model) K.

Definition exhausted_stmt : Prop :=
  forall (fx : FPState) A (s : SX ST) R M model (sp ret this pcons nwords widx icount inst_offset opcode type : Z) (K : TSet),
    callB A s R M model sp ret (dc_stack dc) -> ro_clear L M ->
    getr R 10%bv = Z_to_bv 64 this -> getr R 11%bv = Z_to_bv 64 inst_offset ->
    getr R 12%bv = Z_to_bv 64 opcode -> getr R 13%bv = Z_to_bv 64 type ->
    0 <= inst_offset < 2 ^ 63 -> 0 <= opcode < 2 ^ 16 -> 0 <= type < 2 ^ 32 ->
    placed MI A this 288 -> this + 288 <= 2 ^ 47 -> (forall a, zwin this (this + 288) a -> ~ zwin (sp - dc_stack dc) sp a) ->
    fld M (this + 8) 8 pcons -> fld M (this + 56) 8 nwords -> fld M (this + 72) 8 widx -> fld M (this + 80) 8 icount ->
    0 <= nwords < 2 ^ 63 -> 0 <= widx < 2 ^ 63 -> 0 <= icount < 2 ^ 63 ->
    obj_ok MI A sp (dc_stack dc) pcons 48 -> pcons + 48 <= 2 ^ 47 -> fld M (pcons + 32) 8 0 ->
    ds_room1 A ->
    (forall A' R' M' model' (J : Z -> Prop),
        retB A' s R R' M' model model' ->
        getr R' 10%bv = Z_to_bv 64 (2 ^ 64 - 4) ->
        Permutation (live MI A') (live MI A) ->
        junk_ok MI A J ->
        eff MI A A' M M' (sp - dc_stack dc, sp) (fun a => J a) ->
        srealizes SEGS (cfg fx R' ret M' model') K) ->
    srealizes SEGS (cfg fx R (dc_exhausted dc) M model) K.

End Needs.

Abbreviation sx32 := PrsGrammar.sx32.
Abbreviation ro_span := PrsGrammar.ro_span.
Abbreviation ro_cstr := PrsGrammar.ro_cstr.
Abbreviation leafA := PrsGrammar.leafA.
Abbreviation tabl_consts := PrsGrammar.tabl_consts.
