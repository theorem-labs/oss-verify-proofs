(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "ameta"; "region"; "mslot"; "frame"; "op"; "PGSZ"; "rkind"; "astate"; "am_last"; "padd"; "am_mem"; "kreq"; "fkind"; "am_sc"; "brkst"; "am_maplen"; "UNIT"; "osptr_eqb"; "slotst"; "sptr_eqb"; "ss_fr"; "st_areas"; "rg_kind"; "rg_live"; "Free"; "rg_len"; "nth_slot"; "failure"; "fr_kind"; "st_metas"; "SP"; "am_avail"; "am_freed"; "fr_n"; "fr_off"; "IB"; "prid"; "METAS_PER_AREA"; "am_next"; "am_prev"; "poff"; "st_regions"; "st_avail_meta_area_count"; "st_meta_alloc_shift"; "am_aidx"; "init_state"; "slot_start"; "ss_hdr"; "st_active"; "st_avail_meta_count"; "st_brk"; "stride_of"; "class_size"; "rg_rw"; "st_avail_meta_areas"; "META_SIZE"; "Malloc"; "outcome"; "st_free_meta_head"; "AREA_HDR"; "am_slots"; "st_area_head"; "st_area_tail"; "st_avail_meta"; "st_bounces"; "st_init_done"; "st_mmap_counter"; "st_seq"; "st_unmap_seq"; "st_usage"; "FGroup"; "MMAP_THRESHOLD"; "RkMetaRes"; "mlookup"; "page_round"; "size_classes"; "usage_of"; "znth"; "BrkCur"; "BrkNever"; "MUsed"; "ODone"; "RkMap"; "free"; "mmap_plan"; "ones"; "set_usage"; "zset"; "FFuel"; "FUser"; "IRet"; "MFree"; "OFailed"; "OStarved"; "RkBrk"; "am_set_slots"; "class_of_units"; "find_frame_in"; "initial_cnt"; "itree"; "malloc"; "mkFrame"; "mkRun"; "mkSlot"; "run_script"; "set_bounces"; "set_metas"; "size_to_class"; "sr_state"; "@Corelib.Init.Logic"; "and"; "eq"; "ex"; "not"; "True"; "or"; "False"; "iff"; "@Corelib.Init.Datatypes"; "andb"; "bool"; "option"; "prod"; "cons"; "nat"; "false"; "list"; "true"; "pair"; "nil"; "length"; "Some"; "snd"; "None"; "fst"; "app"; "negb"; "orb"; "unit"; "S"; "tt"; "@Stdlib.ZArith.BinInt.Z"; "add"; "le"; "eqb"; "leb"; "mul"; "lt"; "sub"; "ltb"; "of_nat"; "modulo"; "pow"; "testbit"; "to_nat"; "div"; "lor"; "shiftr"; "land"; "ldiff"; "shiftl"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "mcell"; "MCell"; "VZ"; "LMem"; "LCtx"; "loc"; "region_of"; "usedX"; "zseq"; "implb"; "used_metas"; "optr"; "group_extent"; "loc_addr"; "sval"; "VP"; "hdr_off16"; "allocated"; "memb"; "erase"; "footprint"; "hdr_byte3"; "nodupb"; "VSec"; "brk_regions"; "keys"; "le_byte"; "sval_num"; "CTX_SIZE"; "Inv"; "InvMeta"; "MT"; "MTX"; "U0"; "active_links"; "crange"; "ctx_cells"; "fold_off"; "freering_links"; "group_ok"; "image"; "inside"; "insideb"; "ly_ctx"; "ly_reg"; "mc_loc"; "mc_w"; "nested_at"; "olinks_noneb"; "reserved_ok"; "resv_total"; "ring_fuel"; "ring_list"; "ring_ok"; "ring_okb"; "rings_ok"; "usage_ok"; "CTX_active"; "CTX_avail_meta"; "CTX_avail_meta_area_count"; "CTX_avail_meta_areas"; "CTX_avail_meta_count"; "CTX_bounces"; "CTX_brk"; "CTX_free_meta_head"; "CTX_init_done"; "CTX_meta_alloc_shift"; "CTX_meta_area_head"; "CTX_meta_area_tail"; "CTX_mmap_counter"; "CTX_secret"; "CTX_seq"; "CTX_unmap_seq"; "CTX_usage"; "GMV"; "META_avail"; "META_bits"; "META_freed"; "META_mem"; "META_next"; "META_prev"; "VLo5"; "Xok"; "active_hd"; "active_members"; "active_ring_ok"; "alinks";
"area_index"; "area_ok"; "areas_cells"; "areas_ok"; "cell_holds"; "chain"; "chainb"; "class_ok"; "class_sum"; "collect"; "contrib"; "countb"; "ctx_ok"; "cycle_ok"; "direct_unlinked"; "erase_meta"; "erase_slot"; "flinks"; "frame_ok"; "frame_ptr"; "frames"; "free_members"; "free_meta_keys"; "free_ring_ok"; "get_meta_asserts"; "gm_area_check"; "gm_avail"; "gm_freed"; "gm_last"; "gm_maplen"; "gm_mem"; "gm_off16"; "gm_p3"; "gm_p4"; "gm_sc"; "group_cells"; "handed"; "handed_out"; "in_footprint"; "in_user_block"; "key_placed"; "keys_ok"; "laminar"; "laminarb"; "layout_ok"; "lookup_used"; "ly_sec"; "mapped_ok"; "maps_unique"; "masks_ok"; "mc_val"; "meta_bits"; "meta_key_ok"; "meta_slot_cells"; "nested_ok"; "pairwise"; "parent_slots"; "partial_unique"; "range_mapped"; "ranges_disjoint"; "raw_meta_keys"; "rsv_code"; "slot_cells"; "slot_ok"; "slots_in_class"; "spans_disjoint"; "user_blocks"; "view_of"; "wf_area"; "wf_areas"; "wf_ctx"; "wf_group"; "wf_groups"; "wf_map_regions"; "wf_masks"; "wf_metas"; "wf_rings"; "wf_slot"; "wf_usage"; "wfb"; "@Stdlib.Lists.List"; "forallb"; "In"; "flat_map"; "combine"; "last"; "existsb"; "fold_right"; "NoDup"; "filter"; "hd_error"; "fold_left"; "@Corelib.Lists.ListDef"; "map"; "nth"; "seq"; "Forall"; "repeat"; "@Stdlib.Arith.PeanoNat.Nat"; "eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.Probes"; "srun2"; "listZ_eqb"; "mkRun2"; "s2_err"; "s2_hist"; "s2_ptrs"; "s2_trace"; "irun2"; "kernel_only"; "pingpong"; "run_script2"; "states_eqb"; "ameta_eqb"; "brk_eqb"; "check"; "gen"; "gen_ans"; "mslot_eqb"; "region_eqb"; "run_op2"; "run_states"; "s2_jans"; "s2_kans"; "s2_state"; "slot_eqb"; "states"; "trace_eqb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv.Views"; "MTX"; "@Stdlib.Bool.Bool"; "eqb"; "@Corelib.Init.Peano"; "lt"; "@Corelib.Init.Nat"; "sub"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Definition zseq (lo : Z) (n : Z) : list Z := ltac2:(tb__ "0|0|
S152S7cS0S7cS8dVlo;S95R1A1A2Lk;S154U0S99Vn;A1A2A4").

Fixpoint nodupb {A : Type} (eqb : A -> A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: t => negb (existsb (eqb x) t) && nodupb eqb t
  end.

Definition memb (p : sptr) (l : list sptr) : bool := existsb (sptr_eqb p) l.

Definition countb {A : Type} (f : A -> bool) (l : list A) : Z := Z.of_nat (length (filter f l)).

Definition implb (a b : bool) : bool := negb a || b.
Local Infix "==>" := implb (at level 55, right associativity).

Definition olinks_noneb (l : option sptr * option sptr) : bool := ltac2:(tb__ "0|2|
S77S13S86S79S1A1M0G0Vl;A3S85S1A1M1A2S13S84G0G0Vl;A3G1A2A2").

Definition used_metas (s : astate) : list (sptr * ameta) := ltac2:(tb__ "0|5|
S149S7aS1S4A2M0S7aS1S2A2M1G0G0S7eG1A1M2Le;R1S1S4S4G2Lm;R1S79S1A1M3G3S81G1A1M4Lnext;Lprev;G4S2S7bG1S80S1S2R3R1A4G4A3Lam;X4x3Lm;Lp;X7ax1Le;S1fVs;A1A4").
Definition free_meta_keys (s : astate) : list sptr := ltac2:(tb__ "0|4|
S149S7aS1S4A2M0S1G0G0S7eS1A1M1Le;R1S1S4S4G1Lm;R1S79S1A1M2G2S7bS1R4S81S1A1M3A3Lnext;Lprev;G3S2G3Lm0;X4x3Lm;Lp;X7ax1Le;S1fVs;A1A4").
Definition raw_meta_keys (s : astate) : list sptr := ltac2:(tb__ "0|4|
S149S7aS1S4A2M0S1G0G0S7eS1A1M1Le;R1S1S4S4G1Lm;R1S79S1A1M2G2S81S1A1M3Lnext;Lprev;S7bS1R2G3A3S2G3Lm0;X4x3Lm;Lp;X7ax1Le;S1fVs;A1A4").

Definition lookup_used (s : astate) (p : sptr) : option ameta := ltac2:(tb__ "0|3|
S79S4A1S79S2A1M0Lx;S4bS1fVs;A1Vp;A2S4S4G0Lm;R1S79S1A1M1G1S85S2A1M2Lnext;Lprev;G2S2S83S2R1A2Lam;X4x3Lm;G2X79x2").

Definition region_of (s : astate) (r : nat) : option region := nth_error (st_regions s) r.

Definition allocated (am : ameta) (i : Z) : bool := ltac2:(tb__ "0|0|
S88S98S9bS21Vam;A1S22Vam;A1A2Vi;A2A1").

Definition rsv_code (am : ameta) (fr : frame) : Z := ltac2:(tb__ "0|1|
S93S93S93S35Vam;A1S25A2S91S12S24Vfr;A1A2A2S23Vfr;A1A2S0S78S0L_;S90Z5M0R1A2G0R1X78x2Treserved;").

Definition hdr_byte3 (am : ameta) (i : Z) (fr : frame) : Z := ltac2:(tb__ "0|0|
SeS0Lx;S1eVfr;A1S8dVi;S91Z20S134Vam;Vfr;A2A2A2S8dVi;Zc0A2Xex2").

Definition hdr_off16 (am : ameta) (i : Z) (fr : frame) : Z := ltac2:(tb__ "0|0|
S8dS9aS91S35Vam;A1Vi;A2S12A2S24Vfr;A1A2").

Fixpoint chain (lk : sptr -> option (option sptr * option sptr)) (prev : sptr)
         (l : list sptr) (first : sptr) : Prop :=
  match l with
  | [] => True
  | x :: rest => lk x = Some (Some prev, Some (hd first rest)) /\ chain lk x rest first
  end.

Definition cycle_ok (lk : sptr -> option (option sptr * option sptr)) (ms : list sptr) : Prop := ltac2:(tb__ "0|1|
S6fS14eS1Vms;A2S7eS1A1M0OLms;Vms;S73S1G0SfcVlk;S14bS1Vms;R2A3Vms;R2A4Ll;Lm0;X7ex2A2").

Definition ring_ok (lk : sptr -> option (option sptr * option sptr)) (hd : option sptr)
           (ms : list sptr) : Prop := ltac2:(tb__ "0|0|
S6fS104Vlk;Vms;A2S70S79S1A1Vhd;S150S1Vms;A2A3A2").

Definition olinks_eqb (a b : option (option sptr * option sptr)) : bool := ltac2:(tb__ "0|4|
S79S7aS79S1A1M0G0A2M1A1M2S78La;Va;G1G1S78Lp;R1G0G0G2S78Lb;M3Vb;G1G1S78Lp0;R1G0G0S77S13R5R2A2S13R4R1A2A2Ln2;Lp2;X7ax1Lp0;S7dX79x2Ln1;Lp1;X7ax1Lp;G3Vb;G1S7dLp;S7fX79x2X79x2").

Fixpoint chainb (lk : sptr -> option (option sptr * option sptr)) (prev : sptr)
         (l : list sptr) (first : sptr) : bool :=
  match l with
  | [] => true
  | x :: rest => olinks_eqb (lk x) (Some (Some prev, Some (hd first rest))) && chainb lk x rest first
  end.

Definition ring_okb (lk : sptr -> option (option sptr * option sptr)) (hd : option sptr)
           (ms : list sptr) : bool := ltac2:(tb__ "0|1|
S77Sb6S1S15Vms;A3S7eS1A1M0S78Lms;Vms;S13Vhd;S85S1A1A2S1G0S77S13Vhd;S83S1R2A2A2SfdVlk;S14bS1Vms;R2A3Vms;R2A4A2Ll;Lm0;X7ex2A2").

Fixpoint collect (lk : sptr -> option (option sptr * option sptr)) (fuel : nat)
         (start cur : sptr) (acc : list sptr) : list sptr :=
  match fuel with
  | O => rev (cur :: acc)
  | S f =>
    match lk cur with
    | Some (_, Some nx) => if sptr_eqb nx start then rev (cur :: acc) else collect lk f start nx (cur :: acc)
    | _ => rev (cur :: acc)
    end
  end.

Definition ring_list (lk : sptr -> option (option sptr * option sptr)) (fuel : nat)
           (hd : option sptr) : list sptr := ltac2:(tb__ "0|1|
S79S1A1S7eS1A1Lhd;Vhd;S1S100Vlk;Vfuel;R1R1S81S1A1M0A5Lh;G0X79x2").

Definition ring_fuel (s : astate) : nat := S (length (st_metas s)).

Definition active_links (s : astate) (sc : Z) (p : sptr) : option (option sptr * option sptr) := ltac2:(tb__ "0|4|
S79S2A1S79S7aS79S1A1M0G0A2M1A1M2Lx;S124Vs;Vp;A2S2S78G2L_;S8fSfR1A1Vsc;A2S83G1S80G0G0S29R1A1S28R1A1A4A2S85G1A1M3X78x2Lam;G3X79x2").
Definition freering_links (s : astate) (p : sptr) : option (option sptr * option sptr) := ltac2:(tb__ "0|4|
S79S4A1S79S7aS79S1A1M0G0A2M1A1M2Lx;S4bS1fVs;A1Vp;A2S4S4G2Lm;R1G0G0S83G1S80G0G0R2R1A4A2Lnx;Lpr;S85G1A1M3S2G3Lm0;X4x3Lm;G3X79x2").

Definition active_members (s : astate) (sc : Z) : list sptr := ltac2:(tb__ "0|0|
Sd4Sc2Vs;Vsc;A2Sd3Vs;A1S153S79S1A1S99Vsc;A1S32Vs;A1S85S1A1A4A3").
Definition free_members (s : astate) : list sptr := ltac2:(tb__ "0|0|
Sd4Sc6Vs;A1Sd3Vs;A1S3cVs;A1A3").

Definition wf_ctx (s : astate) : bool := ltac2:(tb__ "0|13|
S77S77S77S77S77S77S77S77S77S77S77S77S77S77S77S77S8fS95S82S79S1A1S32Vs;A1A2A1Z30M0A2S8fS95S82S0S47Vs;A1M1A2A1G0A2A2S8fS95S82S0S46Vs;A1M2A2A1Z20M3A2A2S8fS95S82S0S42Vs;A1M4A2A1G3A2A2S147S0S0S90Z0M5R1A2M6Lu;G1A3A2S147S0S0S77G6S90R1ZffM7A2A2Lu;M8G2A3A2S147S0G8G4A3A2S90G5S45Vs;A1M9A2A2S90G9G7A2A2S90G5S44Vs;A1MaA2A2S94GaS97Z2G3A2A2A2S90G5S2dVs;A1A2A2S90G5S33Vs;A1MbA2A2S90GbS27A2A2S90G5S2cVs;A1McA2A2Sa9S88S43Vs;A1MdA1S77S77S77S7eS7aS1S4A2MeA1MfS78Lx;S1fVs;A1S7fGeGfS7dLl;Lp;X7ex2S7eS1A1M10S78Lx;S17Vs;A1S7fS1G10S7dLl;Ls0;X7ex2A2S10S78Lx;M11S34Vs;A1M12S7fS7dS7cS0S7dLpages;Lr;X10x3A2S8fGcG5A2A2A2A2Sa9GdG11G12S7dS7fS7cS0S7fLpages;Lr;X10x3A2A2").

Definition area_index (s : astate) (a : sptr) : option nat :=
  (fix go (l : list sptr) (k : nat) :=
     match l with
     | [] => None
     | x :: t => if sptr_eqb x a then Some k else go t (S k)
     end) (st_areas s) O.

Definition handed_out (s : astate) (j : nat) : Z := ltac2:(tb__ "0|0|
S78S0L_;S157S8bVj;A1S82S1S17Vs;A1A2A2S93S27S33Vs;A1A2S27X78x2").

Definition meta_key_ok (s : astate) (p : sptr) : bool := ltac2:(tb__ "0|1|
S1S78Lp;Vp;S7cS0S14cS1S1S1S78La;R1S7cS0S77S157R5R2A2S93S93R4R1A2S3dA2S0S77S77S90Z0M0R1A2S8fS96R1S39A2G0A2A2S79S7cA1S78Lx;Sf7Vs;R4A2S7cS94S9aR2S39A2S11cVs;R1A2A2Lj;S7dX79x2A2Td;A2Lao;Lr';X1x1La;S17Vs;A1A3Lo;Lr;X1x1").

Definition wf_metas (s : astate) : bool := ltac2:(tb__ "0|7|
S77S77S77S77Sb6S1S15S152S7aS1S4A2S1S86S1S4A2S1fVs;A1A4M0A3S147S1S12bVs;A1G0A3A2S7eS1A1M1S78Lx;M2S133Vs;A1S7fS1G1S7dLl;Ls0;X7ex2A2S10cVs;A1G1S77S77Sd6Sc6Vs;A1S3cVs;A1R1A3S8fS95S82S1R1A2A1S95S82S1S10dVs;A1M3A2A1A2A2S147S1S1Sb2R1R2A2Lp;G3A3A2Tms;A2G2S17Vs;A1M4S8fS33Vs;A1M5Z0M6A2S1G1S15S41Vs;A1SbS14bS1G4S20U0G6A2A3S8dS3dS91S39S93S27G5A2A2A2A2A2Ll;Ls0;X7ex2A2").

Definition parent_slots (s : astate) (mem : sptr) : list (sptr * ameta * Z) := ltac2:(tb__ "0|4|
S149S7aS1S2A2M0S7aG0S0A2M1G0G0S7eG1A1M2Lgm;R1S1S2S149S0G1S0S79S5A1G2Lx;S16S1cR2R1A2A1S5SeG2Lx;S1eR1A1S81G1A1M3S78G2L_;S15SbS30R3R2A2S91S12S24R1A1A2A2Vmem;A2S7bG1S80G0S0S80S1S2R4R3A4R2A4G3A3G3X78x2Xex2Lfr;G3X79x2Li;Sa8Z0S8dSaR1A1Z1A2A2A4Lam;Lg;X7ax1Lgm;SaaVs;A1A4").

Definition nested_at (s : astate) (p : sptr) : list (sptr * ameta) := ltac2:(tb__ "0|2|
S14fS7aS1S2A2M0G0S77S8fS11S84S1S2R1A3M1A1Z0A2S15ScG1A1Vp;A2A2Lgm;SaaVs;A1A3").

Definition wf_masks (am : ameta) : bool := ltac2:(tb__ "0|2|
SaVam;A1S0S2eVam;A1S0S21Vam;A1S0S22Vam;A1S0S77S77S77S77S77S77S77S77S77S77S90Z0M0R4A2S90R4Z1fA2A2S90G0R3A2A2S90R3R4A2A2S8fS95S82S14S3eVam;A1A2A1S8dR4Z1M1A2A2A2S90G0R2A2A2S90G0R1A2A2S8fS9dR2R1A2G0A2A2S8fS9eS9bR2R1A2S57R4A1A2G0A2A2S8fS9eR2S57R3A1A2G0A2A2S147S0S0S98R2R1A2Li;Sa8S8dR3G1A2S93R4R3A2A2A3A2Tfr;Tav;Taidx;Tlast;").

Definition wf_slot (s : astate) (g : sptr) (am : ameta) (i : Z) : bool := ltac2:(tb__ "0|e|
S1cVam;Vi;A2S14S35Vam;A1S0S77S79S7aS0S0A2M0A1S78Lx;M1S31R2A1G0G0S78Lp;M2R1S0S0S77S77S77S90Z0M3R2A2S90R2ZffM4A2A2S90G3R1A2A2S90R1ZffffM5A2A2Lh16;Lh3;X7ax1Lp;S8fS11Vam;A1G3A2X79x2S79S5A1S78Lx;S16R2A1S5S77S77S77S77S77S77S77Sb1Vam;Vi;A2M6S90G3S23R1A1M7A2A2S90G3S24R1A1M8A2A2S90G8G4A2A2S90S8dS91S12G8A2M9G7A2S93R2S25A2MaA2A2S90Sb0Vam;Vi;R1A3G5A2A2SeS78Lx;S1eR1A1S8fS95S82S7aS1S2A2MbScfVs;SbS30Vam;Vi;A2McG9A2A2A2A1G3A2S77S77S8fG8G3A2MdS8fG7GaA2A2S8fS95S82GbScfVs;GcA2A2A1Z1A2A2Xex2A2Sa9GdG1S31R3A1G0G2R1S0S0S77S8fR2Sb5Vam;Vi;R4A3A2S8fR1Sb0Vam;Vi;R4A3A2A2Lh16;Lh3;X7ax1Lp;S7dX79x2A2A2Lfr;S88G6A1X79x2A2Tstride;Tsl;").

Definition wf_group (s : astate) (g : sptr) (am : ameta) : bool := ltac2:(tb__ "0|17|
S77S77S77S77S141Vam;A1S90Z0M0S11Vam;A1M1A2A2S147S0S144Vs;Vg;Vam;A3Sa8G0S8dSaVam;A1M2Z1M3A2M4A2A3A2S78S78L_;M5S8fSfVam;A1M6Z3fM7A2M8S77S77S77S77S77S8fG2G0A2M9S90G3G1A2A2Sd0S80S79S1A1MaGaS29Vam;A1S28Vam;A1A4A1A2S8fS21Vam;A1G0A2A2S8fS22Vam;A1G0A2A2S79S5A1S78Lx;MbS16S1cVam;G0A2A1S5SeS78Lx;S1eR1A1S77S90S49S23R1A1McA2S94S91G1S7A2MdS8dS8dS8dGcS12A2S25A2S7A2A2A2S7dXex2Lfr;S7dX79x2A2S77S77S77S77S90G0G6A2S94G6Z30A2MeA2Sa9S94S35Vam;A1MfS36G6A1M10A2S77G9Sb1Vam;G0A2A2A2A2Sa9S90G6Z1aA2S89S8fG1G0A2S88G9A1A2A2A2S94S91GfG4A2M11S97Z2Z14A2A2A2X78x2A2G5S94G0G1A2S77S77S1S78Lx;ScVam;A1M12S7cS0S77S8fR1G0A2S79S3A1S78Lx;Sa6Vs;R2A2S3S77S77S8S78Lx;S18R1A1S7dS7dS7fX8x3S19R1A1A2S8fS1bR1A1GdA2A2Lrg;S7dX79x2A2Lo;Lr;X1x1S90S8dS12G11A2GdA2A2Sa9S77G9GeA2S90GdS4cS8dG10S12A2A1A2A2A2S77S88G8A1S7eS7aS7aS1S2A2M13S0A2M14A1M15S78Lx;S12fVs;G12A2S7dG14G15G14S78Lp;R2G13S0G13S78Lp0;R2S1S2G15S78Ll;R5S77S77S94G6SfR1A1M16A2S88S8fG16G7A2A1A2GbS16S1cR1R3A2A1S5S90S93S8dS12S91G10G4A2A2S25A2GcA2Lfr;S7dX79x2A2G14G15S7dLl0;Lp1;X7ex2Lam';Lg';X7ax1Li';Lp0;X7ax1Ll;Lp;X7ex2A2X78x2A2").

Definition group_extent (am : ameta) : Z := ltac2:(tb__ "0|0|
S93S8dS12S91S35Vam;A1S8dSaVam;A1Z1A2A2A2S25A2").

Definition insideb (us : list (sptr * ameta)) (a b : ameta) : bool := ltac2:(tb__ "0|6|
S14cS0S0S79S5A1S78Lx;S16S1cVb;R1A2A1S5SeS78Lx;S1eR1A1S7dS14cS7aS1S2A2M0G0S84S1S2R1A3S2S77S77S77S77S8fS11R1A1Z0M1A2S15ScR1A1M2S30Vb;R4A2A2A2S90S2aG2A1M3S2aScVa;A1A1M4A2A2S90S8dG4SacVa;A1A2S8dG3SacR1A1M5A2A2A2S90G5S23R3A1A2A2Tc;Lcm;Vus;A3Xex2Lfr;S7dX79x2Lj;Sa8G1S8dSaVb;A1Z1A2A2A3").

Definition laminarb (s : astate) : bool := ltac2:(tb__ "0|5|
SaaVs;A1S7eS7aS1S2A2M0A1S147G0G0S147G0G0G0S78Lgm1;R2S1S2G0S78Lgm2;R3S1S2S89S89S89S89S89S15R4R2A2S88S157S26ScR3A1M1A1S26ScR1A1M2A1A2A1A2S90S8dS2aG1A1M3SacR3A1A2S2aG2A1M4A2A2S90S8dG4SacR1A1A2G3A2A2ScaR7R3R1A3A2ScaR7R1R3A3A2La2;Lg2;X7ax1La1;Lg1;X7ax1Lgm2;R2A3Lgm1;R1A3Tus;").

Definition wf_map_regions (s : astate) : bool := ltac2:(tb__ "0|4|
S149S7aS1S2A2M0S7cG0S78S7eS7cA1M1L_;S94Z0S11S84S1S2R1A3M2A1A2S7bS7cS26ScG2A1A1S81S7cA1M3A3G3X78x2Lgm;SaaVs;A1A4G1S77Sb6S7cS157R1A3S147S7cS7cS79S3A1S78Lx;Sa6Vs;R1A2S3S8S78Lx;S18R1A1S7fS7fS174S19R1A1S14cS7cS157R2A1R3A3A2X8x3Lrg;S7fX79x2Lk;S154U0S82S3S2bVs;A1A2A2A3A2Towners;").

Definition wf_groups (s : astate) : bool := ltac2:(tb__ "0|1|
S77S77S147S7aS1S2A2M0G0S13eVs;S86S1S2R1A3S84S1S2R1A3A3Lgm;SaaVs;A1A3S140Vs;A1A2S122Vs;A1A2").

Definition wf_ring (s : astate) (sc : Z) : bool := ltac2:(tb__ "0|9|
S153S79S1A1M0S99Vsc;A1S32Vs;A1S85S1A1A4G0Sf4Vs;Vsc;A2S7eS1A1S77S77Sd6Sc2Vs;Vsc;A2R2R1A3S147S7aS1S2A2M1G1G1S78Lgm;R1S1S2Sa9S8fSfR1A1Vsc;A2S77S77S78S78L_;Sd0S80G0G0S29R1A1S28R1A1A4A1S77S77S88Sb2R2R4A2M2A1S8fS21R1A1Z0M3A2M4A2S8fS22R1A1G3A2M5A2G2X78x2Sa9S88G4A1S13R5S83S1R2A2A2M6A2A2Sa9S77G2S88G6A1A2S88G5A1A2A2A2Lam;Lg;X7ax1Lgm;SaaVs;A1M7A3A2S90S102G1G1S77S8fSfS84S1S2R1A3M8A1Vsc;A2S94S2eG8A1SaG8A1A2A2Lgm;G7A3Z1A2A2Tms;Thd;").

Definition wf_rings (s : astate) : bool := forallb (wf_ring s) (zseq 0 48).

Definition wf_area (s : astate) (a : sptr) : bool := ltac2:(tb__ "0|1|
S1S78La;Va;S7cS0S77S8fS96R1S7A2Z0A2S79S3A1S78Lx;Sa6Vs;R2A2S3S77S77S19R1A1S90S8dR2S7A2S1bR1A1A2A2S8S78Lx;S18R1A1S90S7R2A2M0S77G0S14cS0S8fR2A1S37R1A1A3A2S7dX8x3A2Lrg;S7dX79x2A2Lo;Lr;X1x1").

Definition brk_regions (s : astate) : list nat := ltac2:(tb__ "0|2|
S149S7cS7cS7cS79S3A1S7eS7cA1M0Lx;Sa6Vs;R1A2S3S8G0Lx;S18R1A1S7bS7cR2S81S7cA1M1A3G1G1X8x3Lrg;G1X79x2Lk;S154U0S82S3S2bVs;A1A2A2A4").

Definition wf_areas (s : astate) : bool := ltac2:(tb__ "0|17|
S77S77S77S77S77S77S77S77S147S3S3S90Z0M0S1bR1A1M1A2Lrg;S2bVs;A1M2A3Sb6S1S15S17Vs;A1M3A3A2S147S1S13bVs;A1G3A3A2S13S3fVs;A1S150S1G3A2A2A2S13S40Vs;A1S7eS1A1M4S79S1A1Lx;G3S85S1A1S1G4S83S1S14bS1S7bS1R2R1A3S20U0M5G0A2A3A2Ll0;Ls0;X7ex2A2A2S147S7cS7cS79S3A1M6S78Lx;M7Sa6Vs;R1A2S3S8S78Lx;M8S18R1A1M9S7fS77S77S19R1A1MaS8fS96G1S7A2G0A2A2MbS147S0S0Sb2S20R3R1A2G3A2Lo;S37R1A1McA3A2S7fX8x3Lrg;S7fX79x2Lk;S154G5S82S3G2A2A2MdA3A2S8fS14dS0S7cS7cS0G6S0Lx;Sa6Vs;R2A2MeS3S8S0Lx;G9R2S8dG1R2A2R2X8x3Lrg;R1X79x2Lacc;Lk;G0GdA5S91S91Z2MfS7A2M10S93S97GfS2dVs;A1A2Z1M11A2A2A2A2S7eS7cA1M12S78Lx;Sb8Vs;A1S10S78Lx;M13S34Vs;A1M14S7fS7fS7cS0S7dLpages;Lr;X10x3S7cG12G12S78Ll;R1G7GeS3S77S77S77GbS90G10G1A2A2S147S0S0Sb2S20R4S91S7R1A2M15A2G3A2Lk;Sa8G11S93S9aG1S7A2G11A2A2A3A2G13G14S7dS7fS7cS0S77S157R5R2A2S8fS1bR3A1G15A2A2Lp;Lr';X10x3A2Lrg;S7dX79x2S7cG12S7dLl0;Ln;X7ex2Ll;Lr;X7ex2A2S78S78L_;S94G0S2cVs;A1M16A2S1S78Lx;S38Vs;A1S7cS0G7GeS3S77S77S77S77S77G8G9S7dS7fS7dX8x3GaA2S8fS96R2S7A2G0A2A2S90S7R2A2A2S8fS8dR2S91S7G16A2A2G1A2A2S147S0S0S94R1R3A2Lx;GcA3A2Lrg;S7dX79x2Lo;Lr;X1x1S7fX78x2A2").

Definition slots_in_class (s : astate) (sc : Z) : Z := ltac2:(tb__ "0|2|
S14dS0S7aS1S2A2M0G0S0S78S0L_;S8fSfS84S1S2R2A3M1A1Vsc;A2S8dS8dSaG1A1Z1A2R1A2R1X78x2Lacc;Lgm;Z0SaaVs;A1A5").

Definition wf_usage (s : astate) : bool := ltac2:(tb__ "0|0|
S147S0S0S8fS4eVs;R1A2S137Vs;R1A2A2Lsc;Sa8Z0Z30A2A3").

Definition wfb (s : astate) : bool := ltac2:(tb__ "0|0|
S77S77S77S77S77S13dVs;A1S142Vs;A1A2S13fVs;A1A2S143Vs;A1A2S13cVs;A1A2S145Vs;A1A2").

Inductive loc := LCtx (off : Z) | LMem (p : sptr).

Inductive sval :=
| VZ (z : Z)
| VP (p : sptr)
| VLo5 (z : Z)
| VSec.

Record mcell := MCell { mc_loc : loc; mc_w : nat; mc_val : sval }.

Definition optr (o : option sptr) : sval := ltac2:(tb__ "0|0|
S79S1A1SaeLo;Vo;S1SafR1A1Lp;Sa2Z0A1X79x2").

Definition lpadd (l : loc) (d : Z) : loc := ltac2:(tb__ "0|0|
Sa5Sa5Ll;Vl;S0Sa4S8dR1Vd;A2A1Lo;S1Sa3SbR1Vd;A2A1Lp;Xa5x2").

Definition CTX_secret : Z := 0.
Definition CTX_init_done : Z := 8.
Definition CTX_mmap_counter : Z := 12.
Definition CTX_free_meta_head : Z := 16.
Definition CTX_avail_meta : Z := 24.
Definition CTX_avail_meta_count : Z := 32.
Definition CTX_avail_meta_area_count : Z := 40.
Definition CTX_meta_alloc_shift : Z := 48.
Definition CTX_meta_area_head : Z := 56.
Definition CTX_meta_area_tail : Z := 64.
Definition CTX_avail_meta_areas : Z := 72.
Definition CTX_active : Z := 80.
Definition CTX_usage : Z := 464.
Definition CTX_unmap_seq : Z := 848.
Definition CTX_bounces : Z := 880.
Definition CTX_seq : Z := 912.
Definition CTX_brk : Z := 920.
Definition CTX_SIZE : Z := 928.

Definition META_prev : Z := 0.
Definition META_next : Z := 8.
Definition META_mem : Z := 16.
Definition META_avail : Z := 24.
Definition META_freed : Z := 28.
Definition META_bits : Z := 32.

Definition meta_bits (am : ameta) : Z := ltac2:(tb__ "0|0|
S8dS8dS8dSaVam;A1Z20A2S91Z40SfVam;A1A2A2S91Z1000S11Vam;A1A2A2").

Definition ctx_cells (s : astate) : list mcell := ltac2:(tb__ "0|f|
S87Sa0S7bSa0Sa1Sa4Se6A1U8M0S78SaeL_;M1S43Vs;A1M2Sb7Sa2Z0M3A1M4X78x2A3S7bSa0Sa1Sa4Se1A1U4M5Sa2S78S0L_;G2Z1G3X78x2A1A3S7bSa0Sa1Sa4Se5A1G5Sa2S44Vs;A1A1A3S7bSa0Sa1Sa4Se0A1G0SabS3cVs;A1A1A3S7bSa0Sa1Sa4SdaA1G0S7eS1A1M6SaeLx;S17Vs;A1M7G4S1G6SafS41Vs;A1A1Ll;Ls0;X7ex2A3S7bSa0Sa1Sa4SddA1G0Sa2S33Vs;A1A1A3S7bSa0Sa1Sa4SdbA1G0Sa2S2cVs;A1M8A1A3S7bSa0Sa1Sa4Se2A1G0Sa2S2dVs;A1A1A3S7bSa0Sa1Sa4Se3A1G0SabS3fVs;A1A1A3S7bSa0Sa1Sa4Se4A1G0SabS40Vs;A1A1A3S7bSa0Sa1Sa4SdcA1G0G1S77G6S78Lx;G7S7fS1G6S7dLl;Ls0;X7ex2S8fG8G3A2A2G4SafS38Vs;A1A1X78x2A3S7bSa0Sa1Sa4Se7A1U1M9Sa2S45Vs;A1A1A3S7bSa0Sa1Sa4SdfA1G0S10SaeLx;S34Vs;A1G4Sa2N1A1S7cS0SafS20R2S91S7R1A2A2A1Lp;Lr;X10x3A3S81Sa0A1A3A3A3A3A3A3A3A3A3A3A3A3A3S87Sa0S152S7cSa0S7cSa1Sa4S8dSd9S91Z8S95R1A1MaA2MbA2A1G0SabS153S79S1A1R1S32Vs;A1S85S1A1A4A1A3Lk;S154U0McU30A2MdA4S87Sa0S152S7cSa0S7cSa1Sa4S8dSe9GbA2A1G0Sa2S153S0R1S47Vs;A1G3A4A1A3Lk;GdA4S87Sa0S152S7cSa0S7cSa1Sa4S8dSe8GaA2A1G9Sa2S153S0R1S46Vs;A1G3A4A1A3Lk;S154GcU20A2MeA4S152S7cSa0S7cSa1Sa4S8dSdeGaA2A1G9Sa2S153S0R1S42Vs;A1G3A4A1A3Lk;GeA4A3A3A3A3").

Definition meta_slot_cells (q : sptr) (x : option mslot) : list mcell := ltac2:(tb__ "0|e|
S79S4A1S7eSa0A1M0Lx;Vx;S4S4G0Lm;R1S79S1A1M1G1S7bSa0Sa1Sa3SbVq;Sf0A2A1M2U8M3SabR2A1A3S7bSa0Sa1Sa3SbVq;SefA2A1M4G3SabR1A1A3S7bSa0Sa1Sa3SbVq;SeeA2A1M5G3Sa2Z0A1M6A3S7bSa0Sa1Sa3SbVq;SebA2A1M7U4M8G6A3S7bSa0Sa1Sa3SbVq;SedA2A1M9G8G6A3S7bSa0Sa1Sa3SbVq;SecA2A1MaG3G6A3S81Sa0A1MbA3A3A3A3McA3A3Lnx;Lpr;S7bSa0Sa1G2G3G6A3S7bSa0Sa1G4G3G6A3GcA3A3MdS2S7bSa0Sa1G2G3SabS29R1A1A1A3S7bSa0Sa1G4G3SabS28R1A1A1A3S7bSa0Sa1G5G3SafScR1A1A1A3S7bSa0Sa1G7G8Sa2S21R1A1A1A3S7bSa0Sa1G9G8Sa2S22R1A1A1A3S7bSa0Sa1GaG3Sa2S12aR1A1A1A3GbA3A3A3A3A3A3Lam;X4x3Lm;GdX79x2").

Definition area_cells (s : astate) (a : sptr) (next : option sptr) : list mcell := ltac2:(tb__ "0|1|
S87Sa0S7bSa0Sa1Sa3Va;A1U8M0Sb7A3S7bSa0Sa1Sa3SbVa;Z8A2A1G0SabVnext;A1A3S7bSa0Sa1Sa3SbVa;Z10A2A1U4Sa2S27A1A3S81Sa0A1A3A3A3S149S7cSa0S7cSbVa;S8dS3dS91S39S95R1A1A2A2A2S1S12cR1S4bS1fVs;A1R1A2A2Tq;Lk;S154U0S99S27A1A2A4A3").

Fixpoint areas_cells (s : astate) (l : list sptr) : list mcell :=
  match l with
  | [] => []
  | a :: t => area_cells s a (hd_error t) ++ areas_cells s t
  end.

Definition slot_cells (am : ameta) (i : Z) : list mcell := ltac2:(tb__ "0|b|
S30Vam;Vi;A2S1S1cVam;Vi;A2S14S87Sa0S7bSa0Sa1Sa3SbR2N4M0A2A1U1M1Sa2Z0M2A1M3A3S81Sa0A1M4A3S87Sa0S79S7aS0S0A2M5A1S7eSa0A1M6Lx;S31R1A1G5G5G6Lp;R1S0S0S7bSa0Sa1Sa3SbR5N3M7A2A1G1Sa2R2A1A3S7bSa0Sa1Sa3SbR5N2M8A2A1U2M9Sa2R1A1A3G4A3A3Lh16;Lh3;X7ax1Lp;G4X79x2S79S5A1G6Lx;S16R1A1S5S78G6L_;S8fS24R1A1MaG2A2G4SbR3S91S12GaA2A2S1S7bSa0Sa1Sa3SbR1G0A2A1G1G3A3S7bSa0Sa1Sa3SbR1G7A2A1G1Sa2Sb5Vam;Vi;R2A3A1A3S7bSa0Sa1Sa3SbR1G8A2A1G9Sa2Sb0Vam;Vi;R2A3A1A3G4A3A3A3Tp;X78x2Lfr;G4X79x2A3A3Tsl;Tst;").

Definition group_cells (g : sptr) (am : ameta) : list mcell := ltac2:(tb__ "0|4|
S87Sa0S7bSa0Sa1Sa3ScVam;A1M0A1U8SafVg;A1A3S7bSa0S78Sa0L_;S8fS11Vam;A1Z0M1A2Sa1Sa3SbG0Z8A2A1M2U1Sf1S2eVam;A1M3A1A3Sa1G2U4Sa2G3A1A3X78x2S81Sa0A1A3A3S149S0Sa0S135Vam;A1Sa8G1S8dSaVam;A1Z1A2A2A4A3").

Definition image (s : astate) : list mcell := ltac2:(tb__ "0|1|
S87Sa0Sc4Vs;A1S87Sa0Sf9Vs;S17Vs;A1A2S149S7aS1S2A2M0Sa0G0S11aS86S1S2R1A3S84S1S2R1A3A2Lgm;SaaVs;A1A4A3A3").

Definition footprint (s : astate) : list (loc * Z) := ltac2:(tb__ "0|4|
S7bS7aSa5S0A2M0S80Sa5S0Sa4Z0M1A1SbcA4S87G0S152S1G0S1S80Sa5S0Sa3R1A1S7A4La;S17Vs;A1A4S149S7cG0S7cS79S3A1S7eG0A1M2Lx;Sa6Vs;R1A2S3S8G2Lx;S18R1A1S81G0A1M3G3S78G2L_;S19R1A1S7bG0S80Sa5S0Sa3S20R2G1A2A1S1bR1A1A4G3A3G3X78x2X8x3Lrg;G3X79x2Lk;S154U0S82S3S2bVs;A1A2A2A4A3A3").

Definition user_blocks (s : astate) : list (sptr * Z) := ltac2:(tb__ "0|4|
S149S7aS1S2A2M0S7aS1S0A2M1G0S84S1S2R1A3S2S149S0G1S0S79S5A1S7eG1A1M2Lx;S16S1cR2R1A2A1S5SeG2Lx;S1eR1A1S7bG1S80S1S0SbS30R3R2A2S91S12S24R1A1A2A2S23R1A1A4S81G1A1M3A3G3Xex2Lfr;G3X79x2Li;Sa8Z0S8dSaR1A1Z1A2A2A4Tam;Lgm;SaaVs;A1A4").

Definition live_bytes (s : astate) : Z := ltac2:(tb__ "0|0|
S14dS0S3S3S0S78S0L_;S19R2A1S8dS1bR2A1R1A2R1X78x2Lacc;Lrg;Z0S2bVs;A1A5").

Record layout := Layout {
  ly_ctx : Z;
  ly_reg : nat -> Z;
  ly_brk0 : Z;
  ly_sec : Z;
  ly_top : Z
}.

Definition loc_addr (L : layout) (l : loc) : Z := ltac2:(tb__ "0|0|
Sa5S0Ll;Vl;S0S8dScbVL;A1R1A2Lo;S1S1S0Lp;R1S7cS0S8dSccVL;R2A2R1A2Lo;Lr;X1x1Lp;Xa5x2").

Definition sval_num (L : layout) (v : sval) : Z := ltac2:(tb__ "0|1|
SaeS0Lv;Vv;S0R1Lz;M0S1SadVL;Sa3R1A1A2Lp;G0S125VL;A1Xaex4").

Definition le_byte (z : Z) (w k : nat) : Z := ltac2:(tb__ "0|1|
S96S9cS96Vz;S97Z2S91Z8M0S95Vw;A1A2A2A2S91G0S95Vk;A1A2A2Z100A2").

Definition byteview := Z -> option Z.

Definition cell_holds (L : layout) (m : byteview) (c : mcell) : Prop := ltac2:(tb__ "0|5|
SadVL;ScdVc;A1A2S0SaeOLx;S129Vc;A1S0S7cS175R1SceVc;A1M0A2M1S70S79S0A1M2Vm;S8dR4S95R2A1M3A2A1M4S83S0SbaSbbVL;Sa2R3A1A2G0R2A3A2A3F_;Fk;Lz;S1S7cG1S70G2G4S83S0SbaSbbVL;SafR3A1A2G0R2A3A2A3F_;Fk;Lp;S0S71S0S0S6fS70G2Vm;R3A1S83S0R1A2A3S70S0S96R1Z20A2R2A3A2Lb;A2Lz;S7cG1S70G2Vm;S8dR3G3A2A1S83S0SbaSbbVL;Sb7A2G0R2A3A2A3F_;Fk;Xaex4Ta;").

Definition range_mapped (L : layout) (m : byteview) (rg : loc * Z) : Prop := ltac2:(tb__ "0|1|
S0S6fS8eSadVL;S86Sa5S0Vrg;A3A2M0R1A2S92R1S8dG0S84Sa5S0Vrg;A3A2A2A2S72S70S79S0A1Vm;R2A1S85S0A1A3A1F_;Fx;").

Definition crange (L : layout) (rg : loc * Z) : Z * Z := ltac2:(tb__ "0|0|
S80S0S0SadVL;S86Sa5S0Vrg;A3A2S84Sa5S0Vrg;A3A4").

Definition ranges_disjoint (a b : Z * Z) : Prop := ltac2:(tb__ "0|2|
S74S8eS8dS86S0S0Va;A3M0S84S0S0Va;A3A2S86S0S0Vb;A3M1A2S8eS8dG1S84S0S0Vb;A3A2G0A2A2").

Fixpoint pairwise {A : Type} (R : A -> A -> Prop) (l : list A) : Prop :=
  match l with
  | [] => True
  | x :: t => (forall y, In y t -> R x y) /\ pairwise R t
  end.

Definition layout_ok (L : layout) (s : astate) : Prop := ltac2:(tb__ "0|6|
S6fS70S0S96ScbVL;A1Z8A2Z0M0A3S6fS7cS3S70S79S3A1Sa6Vs;R2A2S83S3R1A2A3S70S78S19R2A1S7fA3S70S0S96SccVL;R4A2S7A2G0A3F_;F_;Frg;Fk;S6fS12eS7aS0S0A2M1S132S152S7aSa5S0A2M2G1Sc3VL;A1Sb4Vs;A1M3A4A3G2S148G2R1G3A3S6fS92G0S86S0S0Sc3VL;R2A2M4A3M5A2S92S8dG5S84S0S0G4A3A2S97Z2Z3fA2A2A2F_;Frg;A2A2A2").

Definition repr (L : layout) (s : astate) (m : byteview) : Prop := ltac2:(tb__ "0|0|
S6fS123VL;Vs;A2S6fS155Sa0SfbVL;Vm;A2Sc8Vs;A1A3S155S7aSa5S0A2S131VL;Vm;A2Sb4Vs;A1A3A2A2").

Definition in_footprint (L : layout) (s : astate) (x : Z) : Prop := ltac2:(tb__ "0|2|
S71S7aSa5S0A2M0G0S6fS148G0R1Sb4Vs;A1A3S6fS8eSadVL;S86Sa5S0R1A3A2M1Vx;A2S92Vx;S8dG1S84Sa5S0R1A3A2A2A2A2Lrg;A2").
Definition in_user_block (L : layout) (s : astate) (x : Z) : Prop := ltac2:(tb__ "0|2|
S71S7aS1S0A2M0G0S6fS148G0R1S139Vs;A1A3S6fS8eSadVL;Sa3S86S1S0R1A3A1A2M1Vx;A2S92Vx;S8dG1S84S1S0R1A3A2A2A2A2Lb;A2").
Definition alloc_owned (L : layout) (s : astate) (x : Z) : Prop := ltac2:(tb__ "0|0|
S6fS11dVL;Vs;Vx;A3S72S11eVL;Vs;Vx;A3A1A2").

Record aux_layout := AuxLayout {
  ax_libc : Z;
  ax_malloc_lock : Z;
  ax_errno : Z;
  ax_size_classes : Z; ax_small_cnt_tab : Z; ax_med_cnt_tab : Z; ax_debruijn32 : Z
}.

Definition erase_slot (sl : slotst) : slotst := ltac2:(tb__ "0|5|
S69S79S7aS0S0A2M0A1M1G1Lx;S31Vsl;A1G0S83G0S80S0S0Z0M2G2A4A2Lp;S85G0A1X79x2S79S5A1M3G3Lx;S16Vsl;A1S5S83S5S67SeS0Lx;S1eR1A1M4G2S24R1A1Xex2S23R1A1G4A3A2Lfr;S85S5A1X79x2A2").

Definition erase_meta (x : mslot) : mslot := ltac2:(tb__ "0|1|
S4S4Lx;Vx;S79S1A1M0G0Vx;Lnext;Lprev;Vx;S2S52S61S152S14S14S107S3eR1A1A4R1A2A1Lam;X4x3").

Definition erase (s : astate) : astate := ltac2:(tb__ "0|1|
S6cS152S7aS1S4A2M0G0G0S80S1S4S86S1S4R1A3S106S84S1S4R1A3A1A4Le;S1fVs;A1A4Vs;A2").

Definition shape_eq (s t : astate) : Prop := ltac2:(tb__ "0|0|
S70S9Sb3Vs;A1Sb3Vt;A1A3").

Record get_meta_view := GMV {
  gm_p4 : Z; gm_p3 : Z; gm_off16 : Z;
  gm_meta : sptr;
  gm_mem : sptr; gm_avail : Z; gm_freed : Z;
  gm_last : Z; gm_sc : Z; gm_maplen : Z;
  gm_area_check : Z
}.

Definition get_meta_asserts (p base : sptr) (v : get_meta_view) : bool := ltac2:(tb__ "0|8|
S77S77S77S77S77S77S77S77S8fS96S2aVp;A1Z10M0A2Z0M1A2S8fS118Vv;A1G1A2A2S15S115Vv;A1Vbase;A2A2S90S9dS117Vv;A1Z1fA2M2S113Vv;A1A2A2S88S98S111Vv;A1G2A2A1A2S88S98S112Vv;A1G2A2A1A2S8fS110Vv;A1G1A2A2S78S78L_;S94S119Vv;A1M3Z30A2S77S90S91S4fG3S4dA2M4G2A2S116Vv;A1M5A2S94G5S91G4S8dG2Z1M6A2A2A2A2S8fG3Z3fA2X78x2A2Sa9S94G1S114Vv;A1M7A2S90G5S93S9aS91G7Z1000A2G0A2G6A2A2A2A2").

Definition view_of (s : astate) (g : sptr) (am : ameta) (i : Z) (fr : frame) : get_meta_view := ltac2:(tb__ "0|1|
SeaZ0M0Sb5Vam;Vi;Vfr;A3Sb0Vam;Vi;Vfr;A3Vg;ScVam;A1S21Vam;A1S22Vam;A1SaVam;A1SfVam;A1S11Vam;A1G0Ab").

Definition answer_ok (q : kreq) (z : Z) : Prop := ltac2:(tb__ "0|1|
SdOLq;Vq;S73S0S73Lnpages;S73S0S73Llen;M0G0S1S73Lpage;S7cG0Lr;S0S6fS8eZ0Vz;A2S92Vz;Z100A2A2Lpristine;Xdx8").

Fixpoint safe {A : Type} (t : itree astate A) : Prop :=
  match t with
  | IRet _ => True
  | IFail _ => False
  | IAsk q _ k => forall z, answer_ok q z -> safe (k z)
  end.

Fixpoint yields {A : Type} (t : itree astate A) (tr : list (kreq * Z)) (a : A) : Prop :=
  match t, tr with
  | IRet a', [] => a' = a
  | IAsk q _ k, (q', z) :: tr' => q' = q /\ answer_ok q z /\ yields (k z) tr' a
  | _, _ => False
  end.

Definition resv_total (s : astate) : Z := ltac2:(tb__ "0|0|
S14dS0S3S3S0S8S0Lx;S18R2A1R1S8dS1bR2A1R1A2R1X8x3Lacc;Lrg;Z0S2bVs;A1A5").

Definition req_ok (s : astate) (q : kreq) : Prop := ltac2:(tb__ "0|11|
SdOLq;Vq;S6fS70S10S34Vs;A1M0S51A3S70S7eS7cA1Sb8Vs;A1S81S7cA1A3A2M1S0S74S6fS70S0R1Z2M2A3G1A2S6fS70S0R1Z1M3A3S71S7cS7cS71S0S0S71S3S3S6fS70S10G0S50R3R2A2A3S6fS70S79S3A1M4Sa6Vs;R3A2S83S3R1A2M5A3M6S6fS70S8S18R1A1M7S60A3M8S6fS70S78S19R1A1S7fA3M9S70S0S1bR1A1MaS91S7R2A2A3A2A2A2A2Lrg;A2Lp;A2Lr;A2A2A2Ln;S71S7cS7cS71S3S3S6fS70S10G0S50R2G2A2A3S6fS70S7cS8bR2A1S82S3S2bVs;A1A2A3S6fS70G4Sa6Vs;R2A2G5A3S6fG8S6fS70S0GaS91G2S7A2MbA3S155S1S1S72S70S7cS26R1A1R3A3A1La;S17Vs;A1A3A2A2A2A2A2Lrg;A2Lr;A2S0S6fS8eG3R1A2S92R1S97G2Z3fA2A2A2Llen;S0S6fS70S0R1S91S9fG2S2dVs;A1McA2S7A2A3S6fS70S0S2cVs;A1MdZ0MeA3S6fS8eGeGcA2S70S0Sd2Vs;A1S91GbS93S97G2GcA2G3A2A2A3A2A2A2Llen;S1S6fS92GeGdA2S6fS70S1R1S38Vs;A1A3S71S3S3S6fS70G4Sa6Vs;S26R2A1A2G5A3S6fS70S8G7S4aA3S6fG9S6fS70S0S96S2aR2A1MfS7A2GeA3S6fS8eS7GfA2S6fS8eS8dGfS7A2GaA2S72S148S0GfS37R1A1A3A1A2A2A2A2A2A2Lrg;A2A2A2Lp;S7cS0S71S3S3S6fG6S6fS70S8G7S54A3S6fG9S6fS70S0GaS4cR2A1A3S6fS8eGeR2A2S155S7aS1S2A2M10G10S92GeS11S84S1S2R1A3A1A2S72S70S7cS26ScS84S1S2R2A3A1A1R5A3A1F_;Lgm;SaaVs;A1A3A2A2A2A2A2Lrg;A2Llen;Lr;S0S73Lpristine;Xdx8").

Fixpoint reqs_ok {A : Type} (t : itree astate A) : Prop :=
  match t with
  | IAsk q snap k => req_ok snap q /\ forall z, answer_ok q z -> reqs_ok (k z)
  | _ => True
  end.

Fixpoint tsim {A B : Type} (R : A -> B -> Prop) (t : itree astate A) (u : itree astate B) : Prop :=
  match t, u with
  | IRet a, IRet b => R a b
  | IAsk (KJunk _) _ k, IAsk (KJunk _) _ k' =>
      forall z z', 0 <= z < 256 -> 0 <= z' < 256 -> tsim R (k z) (k' z')
  | IAsk q _ k, IAsk q' _ k' => q = q' /\ forall z, tsim R (k z) (k' z)
  | IFail _, IFail _ => True
  | _, _ => False
  end.

Definition frames (s : astate) : list (sptr * ameta * Z * frame) := ltac2:(tb__ "0|5|
S149S7aS1S2A2M0S7aS7aG0S0A2M1S5A2M2G0G0S7eG2A1M3Lgm;R1S1S2S149S0G2S0S79S5A1G3Lx;S16S1cR2R1A2A1S5S7bG2S80G1S5S80G0S0S80S1S2R4R3A4R2A4R1A4S81G2A1M4A3Lfr;G4X79x2Li;Sa8Z0S8dSaR1A1Z1A2A2A4Lam;Lg;X7ax1Lgm;SaaVs;A1A4").

Definition frame_ptr (am : ameta) (i : Z) (fr : frame) : sptr := ltac2:(tb__ "0|0|
SbS30Vam;Vi;A2S91S12S24Vfr;A1A2A2").

Definition cell_range (L : layout) (c : mcell) : Z * Z := ltac2:(tb__ "0|0|
S80S0S0SadVL;ScdVc;A1A2S95SceVc;A1A1A4").
Definition block_range (L : layout) (b : sptr * Z) : Z * Z := ltac2:(tb__ "0|0|
S80S0S0SadVL;Sa3S86S1S0Vb;A3A1A2S84S1S0Vb;A3A4").
Definition range_incl (a b : Z * Z) : Prop := ltac2:(tb__ "0|2|
S6fS8eS86S0S0Vb;A3M0S86S0S0Va;A3M1A2S8eS8dG1S84S0S0Va;A3A2S8dG0S84S0S0Vb;A3A2A2A2").

Definition bounded (s : astate) : Prop := ltac2:(tb__ "0|5|
S6fS0S6fS8eZ0M0S4eVs;R1A2M1A2S92G1S97Z2M2Z30A2A2A2Fsc;S6fS6fS8eG0S2dVs;A1M3A2S8eG3Z22A2A2S6fS92S95S82S1S17Vs;A1M4A2A1S97G2Z23A2A2S74S6fS70S7eS1A1G4S81S1A1A3S70S0S2cVs;A1G0A3A2S175S26S38Vs;A1A1S82S3S2bVs;A1A2A2A2A2A2A2").

Definition MT (s : astate) : sptr -> option mslot := mlookup (st_metas s).
Definition keys (s : astate) : list sptr := map fst (st_metas s).

Section Views.
  Variable X : list sptr.
  Variable s : astate.

  Definition MTX (g : sptr) : option mslot := ltac2:(tb__ "0|0|
S78S79S4A1L_;Sb2Vg;VX;A2S85S4A1SbfVs;Vg;A2X78x2").

  Definition usedX (g : sptr) (am : ameta) : Prop := ltac2:(tb__ "0|0|
S70S79S4A1S173Vg;A1S83S4S52Vam;A1A2A3").

  Definition alinks (sc : Z) (g : sptr) : option (option sptr * option sptr) := ltac2:(tb__ "0|4|
S79S4A1S79S7aS79S1A1M0G0A2M1A1M2Lx;S173Vg;A1S4S4G2Lm;R1G0G0S85G1A1M3Lnext;Lprev;G3S2S78G2L_;S8fSfR1A1Vsc;A2S83G1S80G0G0S29R1A1S28R1A1A4A2G3X78x2Lam;X4x3Lm;G3X79x2").
  Definition flinks (g : sptr) : option (option sptr * option sptr) := ltac2:(tb__ "0|4|
S79S4A1S79S7aS79S1A1M0G0A2M1A1M2Lx;S173Vg;A1S4S4G2Lm;R1G0G0S83G1S80G0G0R2R1A4A2Lnx;Lpr;S85G1A1M3S2G3Lm0;X4x3Lm;G3X79x2").
End Views.

Definition active_hd (s : astate) (sc : Z) : option sptr := ltac2:(tb__ "0|0|
S153S79S1A1S99Vsc;A1S32Vs;A1S85S1A1A4").

Definition masks_ok (am : ameta) : Prop := ltac2:(tb__ "0|9|
S6fS6fS8eZ0M0SaVam;A1M1A2S8eG1Z1fA2A2S6fS6fS8eG0S2eVam;A1M2A2S8eG2G1A2A2S6fS70S7cS82S14S3eVam;A1A2S99S8dG1Z1A2A1A3S6fS8eG0S21Vam;A1M3A2S6fS8eG0S22Vam;A1M4A2S6fS0S8eG0R1A2S70S78S98G3R2A2M5S7fA3S70S78S98G4R3A2S7dA3F_;F_;Fi;S6fS0S92G1R1A2S6fS70S78G5S7dA3M6S70S78S98G4R2A2M7S7dA3A2F_;Fi;S6fS0S92G2R1A2M8G6F_;Fi;S0S6fG8S8eR1G1A2A2S70S78G7S7fA3F_;Fi;A2A2A2A2A2A2A2A2").

Definition frame_ok (am : ameta) (i : Z) (fr : frame) : Prop := ltac2:(tb__ "0|4|
S6fS8eZ0M0S23Vfr;A1M1A2S6fS6fS8eG0S24Vfr;A1M2A2S8eG2ZffA2A2S6fS8eS8dS91S12G2A2G1A2S93S35Vam;A1S25A2M3A2S6fS8eSb0Vam;Vi;Vfr;A3ZffffA2S70SeS1eVfr;A1S48A3S6fS70S0G2G0A3S70S0G1G3A3A2F_;A2A2A2A2").

Definition slot_ok (R : option (sptr * Z)) (g : sptr) (am : ameta) (i : Z) : Prop := ltac2:(tb__ "0|7|
S1cVam;Vi;A2S14S6fS70S79S7aS0S0A2M0A1M1S31R1A1S85G0A1A3S70S0S11Vam;A1Z0M2A3F_;S6fS0S0S70G1S31R3A1M3S83G0S80S0S0R2R1A4A2A3S6fS6fS8eG2R3A2S8eR3ZffA2A2S6fS8eG2R2A2S8eR2ZffffA2A2A2F_;Fh16;Fh3;S79S5A1OLx;S16R1A1S5S6fS70S78Sb1Vam;Vi;A2M4S7fA3S6fS72S70S79S7aS1S0A2M5A1VR;S83G5S80S1S0Vg;Vi;A4A2A3M6A1S6fS109Vam;Vi;R1A3S70S0S24R1A1G2A3S70G1G3S83G0S80S0S0Sb5Vam;Vi;R2A3Sb0Vam;Vi;R2A3A4A2A3F_;A2A2A2Lfr;S74S70S78G4S7dA3G6A2X79x2A2A2Tsl;").

Definition class_ok (R : option (sptr * Z)) (g : sptr) (am : ameta) : Prop := ltac2:(tb__ "0|9|
S74S6fS70S0SfVam;A1M0Z3fA3S6fS70S0SaVam;A1M1Z0M2A3M3S6fS8eZ1M4S11Vam;A1M5A2S6fS70S0S21Vam;A1G2A3S6fS70S0S22Vam;A1G2A3S74S70S79S7aS1S0A2M6A1VR;S83G6S80S1S0Vg;G2A4A2A3S71S5S5S6fS70S79S5A1S16S1cVam;G2A2A1S83S5R1A2A3S6fS70SeS1eR1A1S5bA3S6fS8eS49S23R1A1M7A2S92S91G5S7A2S8dS8dS8dG7S12A2S25A2S7A2A2A2A2A2Lfr;A2A2A2A2A2A2A2S6fS6fS8eG2G0A2S92G0Z30A2A2S6fS92S35Vam;A1M8S36G0A1A2S6fG3S70S78Sb1Vam;G2A2S7fA3A2F_;S6fS8eG0Z1aA2S74S70S0G5G2A3S72G3A1A2F_;S92S91G8S8dG1G4A2A2S97Z2Z14A2A2A2A2A2A2").

Definition mapped_ok (s : astate) (am : ameta) : Prop := ltac2:(tb__ "0|5|
S92Z0M0S11Vam;A1M1A2S71S7cS7cS71S3S3S6fS70S1ScVam;A1S20R2G0A2A3S6fS70S79S3A1Sa6Vs;R2A2S83S3R1A2A3S6fS70S8S18R1A1S54A3S6fS70S78S19R1A1S7fA3S6fS70S0S1bR1A1S91G1S7A2M2A3S6fS8eS8dS12S91S35Vam;A1S8dSaVam;A1M3Z1A2A2A2G2A2S70S0G3G0A3S92SfVam;A1M4Z30A2S8eG2S4cS8dS36G4A1S12A2A1A2F_;F_;A2A2A2A2A2A2Lrg;A2Lr;A2F_;").

Definition nested_ok (X : list sptr) (s : astate) (am : ameta) : Prop := ltac2:(tb__ "0|4|
S70S0S11Vam;A1Z0M0A3S6fS72S70S0SfVam;A1M1Z3fM2A3A1S71S1S1S71S2S2S71S0S0S71S5S5S6fSa7VX;Vs;R4R3A4S6fS6fS8eG0R2A2S8eR2SaR3A1A2A2S6fS70S79S5A1S16S1cR3R2A2A1S83S5R1A2A3S6fS70SeS1eR1A1S48A3S6fS70S1ScVam;A1S30R3R2A2A3S6fS92G1SfR3A1M3A2S6fS72S70S0G3G2A3A1S8eS93S8dS12S91S36G1A1S8dSaVam;A1Z1A2A2A2S25A2S23R1A1A2A2A2A2A2A2A2A2Lfr';A2Li';A2Lam';A2Lg';A2A2F_;").

Definition group_ok (X : list sptr) (R : option (sptr * Z)) (s : astate) (g : sptr) (am : ameta) : Prop := ltac2:(tb__ "0|1|
S6fS128Vam;A1S6fS8eZ0M0S11Vam;A1A2S6fS0S6fS8eG0R1A2S8eR1SaVam;A1A2A2S136VR;Vg;Vam;R2A4F_;Fi;S6fSfeVR;Vg;Vam;A3S6fS126Vs;Vam;A2S12dVX;Vs;Vam;A3A2A2A2A2A2").

Definition inside (X : list sptr) (s : astate) (a b : ameta) : Prop := ltac2:(tb__ "0|5|
S71S0S0S71S5S5S71S1S1S71S2S2S6fS6fS8eZ0M0R4A2S8eR4SaVb;A1A2A2S6fS70S79S5A1S16S1cVb;R4A2A1S83S5R3A2A3S6fS70SeS1eR3A1S48A3S6fSa7VX;Vs;R2R1A4S6fS70S0S11R1A1G0A3S6fS70S1ScR1A1M1S30Vb;R4A2A3S6fS8eS2aG1A1M2S2aScVa;A1A1M3A2S6fS8eS8dG3SacVa;A1A2S8dG2SacR1A1M4A2A2S8eG4S23R3A1A2A2A2A2A2A2A2A2A2Lac;A2Lc;A2Lfr;A2Lj;A2").

Definition spans_disjoint (a b : ameta) : Prop := ltac2:(tb__ "0|2|
S74S8eS8dS2aScVa;A1A1M0SacVa;A1A2S2aScVb;A1A1M1A2S8eS8dG1SacVb;A1A2G0A2A2").

Definition laminar (X : list sptr) (s : astate) : Prop := ltac2:(tb__ "0|0|
S1S2S1S2Sa7VX;Vs;R4R3A4Sa7VX;Vs;R3R2A4S72S70S1R6R4A3A1S70S7cS26ScR6A1A1S26ScR4A1A1A3S74S138R7R5A2S74Sc9VX;Vs;R7R5A4Sc9VX;Vs;R5R7A4A2A2F_;F_;F_;F_;Fa2;Fg2;Fa1;Fg1;").

Definition maps_unique (X : list sptr) (s : astate) : Prop := ltac2:(tb__ "0|1|
S1S2S1S2Sa7VX;Vs;R4R3A4Sa7VX;Vs;R3R2A4S92Z0M0S11R5A1A2S92G0S11R4A1A2S70S7cS26ScR7A1A1S26ScR5A1A1A3S70S1R9R7A3F_;F_;F_;F_;F_;Fa2;Fg2;Fa1;Fg1;").

Definition free_ring_ok (X : list sptr) (s : astate) : Prop := ltac2:(tb__ "0|2|
S71S7eS1A1M0G0S6fSd5S108VX;Vs;A2S3cVs;A1R1A3S1S79S1A1M1G1S70S79S4A1Sc0VX;Vs;R3A3S83S4S5dR2R1A2A2A3S148S1R4R5A3F_;Fnx;Fpr;Fg;A2Lms;A2").

Definition active_ring_ok (X : list sptr) (R : option (sptr * Z)) (s : astate) (sc : Z) : Prop := ltac2:(tb__ "0|a|
S71S7eS1A1M0G0S6fSd5Sf6VX;Vs;Vsc;A3Sf3Vs;Vsc;A2M1R1A3S6fS1S2Sa7VX;Vs;R2R1A4M2S70S0SfR2A1Vsc;A3M3S76S148S1R4R5A3M4S72S70S7aS79S1A1M5G5A2S80G5G5S29R3A1S28R3A1A4S80G5G5S85S1A1M6G6A4A3A1A2F_;F_;Fam;Fg;S6fS1S2G2G3S72G4A1S6fS70S0S21R4A1Z0M7A3S70S0S22R4A1G7A3A2F_;F_;F_;Fam;Fg;S6fS1S2G2G3S72S70S0S21R3A1G7A3A1S70G5G1S83S1R5A2A3M8F_;F_;F_;Fam;Fg;S1S2G2G3G4S72G8A1S0S72S70S79S7aS1S0A2M9A1VR;S83G9S80S1S0R7R1A4A2A3A1Fi;S72S70S0S22R6A1G7A3A1F_;F_;F_;F_;F_;Fam;Fg;A2A2A2A2Lms;A2").

Definition partial_unique (X : list sptr) (s : astate) : Prop := ltac2:(tb__ "0|0|
S1S2S1S2Sa7VX;Vs;R4R3A4Sa7VX;Vs;R3R2A4S70S0SfR5A1SfR3A1A3S92S2eR6A1SaR6A1A2S92S2eR5A1SaR5A1A2S70S1R9R7A3F_;F_;F_;F_;F_;Fa2;Fg2;Fa1;Fg1;").

Definition direct_unlinked (X : list sptr) (s : astate) : Prop := ltac2:(tb__ "0|2|
S1S2Sa7VX;Vs;R2R1A4S70S0SfR2A1Z3fA3S6fS70S79S1A1M0S29R3A1S85S1A1M1A3S70G0S28R3A1G1A3A2F_;F_;Fam;Fg;").

Definition rings_ok (X : list sptr) (R : option (sptr * Z)) (s : astate) : Prop := ltac2:(tb__ "0|0|
S6fS10eVX;Vs;A2S6fS0S6fS8eZ0R1A2S92R1Z30A2A2Sf5VX;VR;Vs;R2A4F_;Fsc;S105VX;Vs;A2A2A2").

Definition handed (s : astate) (a : sptr) : Z := ltac2:(tb__ "0|0|
S78S0L_;S15Va;S14bS1S17Vs;A1S20U0Z0A2A3A2S93S27S33Vs;A1A2S27X78x2").

Definition key_placed (s : astate) (p : sptr) : Prop := ltac2:(tb__ "0|0|
S71S1S1S71S0S0S6fS148S1R2S17Vs;A1A3S6fS6fS8eZ0R1A2S92R1S11bVs;R2A2A2A2S70S1Vp;SbR2S8dS3dS91S39R1A2A2A2A3A2A2Lk;A2La;A2").

Definition keys_ok (s : astate) : Prop := ltac2:(tb__ "0|5|
S6fS14eS1Sb9Vs;A1M0A2S6fS1S148S1R1G0A3S11fVs;R2A2F_;Fp;S6fS70S7eS1A1S17Vs;A1M1S81S1A1A3M2S70S0S33Vs;A1M3Z0M4A3F_;S6fS72G2A1S70S1S41Vs;A1SbS14bS1G1S20U0G4A2A3S8dS3dS91S39S93S27G3A2A2A2A2A3F_;S6fS8eG4G3A2S8eG3S27A2A2A2A2A2A2").

Definition Xok (X : list sptr) (s : astate) : Prop := ltac2:(tb__ "0|3|
S1S148S1R1VX;A3S6fS148S1R2Sb9Vs;A1A3S79S4A1OLx;SbfVs;R2A2S4S4OLm;R1S79S1A1M0G0G0OLprev;R2S1S75Ls0;M1G0OLnext;R1G1S73X79x2X79x2Lnext;Lprev;S73S2S6fS70G0S29R1A1S85S1A1M2A3S6fS70G0S28R1A1G2A3S0S70S79S5A1S16S1cR2R1A2A1S85S5A1A3Fi;A2A2Lam;X4x3Lm;S75X79x2A2F_;Fx;").

Definition area_ok (s : astate) (a : sptr) : Prop := ltac2:(tb__ "0|0|
S71S7cS7cS71S0S0S71S3S3S6fS70S1Va;S20R3R2A2A3S6fS70S0S96R2S7A2Z0A3S6fS8eS7R2A2S6fS70S79S3A1Sa6Vs;R3A2S83S3R1A2A3S6fS70S78S19R1A1S7fA3S6fS8eS8dR2S7A2S1bR1A1A2S8OLx;S18R1A1S73S148S0R2S37R1A1A3S75X8x3A2A2A2A2A2A2Lrg;A2Lo;A2Lr;A2").

Definition areas_ok (s : astate) : Prop := ltac2:(tb__ "0|12|
S6fS14eS1S17Vs;A1M0A2S6fS1S148S1R1G0A3Sf8Vs;R2A2F_;Fa;S6fS70S79S1A1M1S3fVs;A1S150S1G0A2A3S6fS70G1S40Vs;A1S7eS1A1M2G1Lx;G0S85S1A1S1G2S83S1S14bS1S7bS1R2R1A3S20U0Z0M3A2A3A2Ll0;Ls0;X7ex2A3S6fS7cS3S70S79S3A1M4Sa6Vs;R2A2S83S3R1A2M5A3M6S70S8S18R2A1S4aA3S6fS70S78S19R3A1S7fA3S6fS70S0S96S1bR3A1M7S7A2G3A3S8eG3G7A2A2A2F_;F_;Frg;Fk;S6fS70S0Sd2Vs;A1S91S91Z2M8S7A2M9S93S97G8S2dVs;A1A2Z1A2A2A3S6fS10OLx;S34Vs;A1S70S7eS7cA1MaSb8Vs;A1MbS81S7cA1McA3S7cS148S7cR1GbA3S6fS70GaGbS7bS7cR2GcA3A3MdS71S3S3S6fS70G4Sa6Vs;R3A2G5A3MeS6fS70S78S19R1A1S7fA3MfS6fS70S0S96S1bR1A1M10S7A2G3A3S8eG9G10A2A2A2A2Lrg;A2A2F_;Fr;S7cS0S6fGdS71S3S3S6fGeS6fGfS6fS70S0G10S91S7R2A2A3S8eG8R2A2A2A2A2Lrg;A2A2Lp;Lr;X10x3S6fS92G3S2cVs;A1M11A2S71S7cS7cS71S0S0S71S3S3S6fS70S1S38Vs;A1S20R3R2A2A3S6fGeS6fS70S8S18R1A1S4aA3S6fGfS6fS70S0S96R2S7A2G3A3S6fS8eS7R2A2S6fS70S0S8dR2S91S7G11A2A2G10A3S0S148S0R1S37R2A1A3S92R2R4A2F_;Fx;A2A2A2A2A2A2A2Lrg;A2Lo;A2Lr;A2F_;S7cS3G6S8eG3S1bR2A1A2F_;Frg;Fk;A2A2A2A2A2A2A2A2").

Definition ctx_ok (s : astate) : Prop := ltac2:(tb__ "0|f|
S6fS70S7cS82S79S1A1S32Vs;A1A2U30M0A3S6fS70S7cS82S0S47Vs;A1M1A2G0A3S6fS70S7cS82S0S46Vs;A1M2A2U20M3A3S6fS70S7cS82S0S42Vs;A1M4A2G3A3S6fS0S148S0R1G1A3S8eZ0M5R2A2M6F_;Fu;S6fS0S148S0R1G2A3S6fG6S8eR2ZffM7A2A2M8F_;Fu;S6fS0S148S0R1G4A3G8F_;Fu;S6fS6fS8eG5S45Vs;A1M9A2S8eG9G7A2A2S6fS6fS8eG5S44Vs;A1MaA2S92GaS97Z2Z20A2A2A2S6fS8eG5S2dVs;A1A2S6fS8eG5S2cVs;A1MbA2S6fS70S78S43Vs;A1McS7dA3S6fS70S7eS7aS1S4A2MdA1S1fVs;A1S81GdA1A3S6fS70S7eS1A1S17Vs;A1S81S1A1A3S6fS70S10S34Vs;A1S51A3MeS70S0GbG5A3A2A2A2F_;S70S78GcS7fA3S72GeA1F_;A2A2A2A2A2A2A2A2A2A2A2A2").

Definition contrib (X : list sptr) (s : astate) (sc : Z) (g : sptr) : Z := ltac2:(tb__ "0|2|
S79S4A1S0Lx;Sc0VX;Vs;Vg;A3S4S4S0Lm;R1S79S1A1M0G0Z0M1Lnext;Lprev;G1S2S78S0L_;S8fSfR1A1Vsc;A2S8dSaR1A1Z1A2G1X78x2Lam;X4x3Lm;G1X79x2").

Definition class_sum (X : list sptr) (s : astate) (sc : Z) : Z := ltac2:(tb__ "0|0|
S14dS0S1S1S0S8dS101VX;Vs;Vsc;R2A4R1A2Lacc;Lg;Z0Sb9Vs;A1A5").

Definition usage_ok (X : list sptr) (U : Z -> Z) (s : astate) : Prop := ltac2:(tb__ "0|0|
S0S6fS8eZ0R1A2S92R1Z30A2A2S70S0S4eVs;R2A2S8dSffVX;Vs;R2A3VU;R2A1A2A3F_;Fsc;").

Definition U0 : Z -> Z := fun _ => 0.

Definition reserved_ok (X : list sptr) (R : option (sptr * Z)) (s : astate) : Prop := ltac2:(tb__ "0|1|
S1S0S70S79S7aS1S0A2M0A1VR;S83G0S80S1S0R2R1A4A2A3S71S2S2S6fSa7VX;Vs;R4R1A4S6fS6fS8eZ0R3A2S8eR3SaR1A1A2A2S6fS70S79S5A1S16S1cR1R3A2A1S85S5A1A3S70S78Sb1R1R3A2S7fA3A2A2A2Lam;A2F_;Fi;Fg;").

Definition InvMeta (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) : Prop := ltac2:(tb__ "0|0|
S6fSf2VX;Vs;A2S6fS1S2Sa7VX;Vs;R2R1A4Sc7VX;VR;Vs;R3R2A5F_;Fam;Fg;S6fS121VX;Vs;A2S6fS127VX;Vs;A2S6fSd7VX;VR;Vs;A3S6fSd8VX;VU;Vs;A3S6fSd1VX;VR;Vs;A3S130VX;Vs;A2A2A2A2A2A2A2A2").

Definition Inv (X : list sptr) (R : option (sptr * Z)) (U : Z -> Z) (s : astate) : Prop := ltac2:(tb__ "0|0|
S6fS103Vs;A1S6fS120Vs;A1S6fSfaVs;A1SbeVX;VR;VU;Vs;A4A2A2A2").

Definition WFI (s : astate) : Prop := ltac2:(tb__ "0|0|
SbdS81S1A1S85S7aS1S0A2A1Sc1Vs;A4").

Section Proj.
  Context {X : list sptr} {R : option (sptr * Z)} {U : Z -> Z} {s : astate} (H : Inv X R U s).
  Lemma inv_ctx : ctx_ok s. Proof using H. exact (proj1 H). Qed.
  Lemma inv_keys : keys_ok s. Proof using H. exact (proj1 (proj2 H)). Qed.
  Lemma inv_areas : areas_ok s. Proof using H. exact (proj1 (proj2 (proj2 H))). Qed.
  Lemma inv_meta : ltac2:(tb__ "0|0|
SbeVX;VR;VU;Vs;A4"). Proof using H. exact (proj2 (proj2 (proj2 H))). Qed.
  Lemma inv_X : Xok X s. Proof using H. exact (proj1 inv_meta). Qed.
  Lemma inv_groups : ltac2:(tb__ "0|0|
S1S2Sa7VX;Vs;R2R1A4Sc7VX;VR;Vs;R3R2A5F_;Fam;Fg;").
  Proof using H. exact (proj1 (proj2 inv_meta)). Qed.
  Lemma inv_laminar : laminar X s. Proof using H. exact (proj1 (proj2 (proj2 inv_meta))). Qed.
  Lemma inv_maps : maps_unique X s. Proof using H. exact (proj1 (proj2 (proj2 (proj2 inv_meta)))). Qed.
  Lemma inv_rings : ltac2:(tb__ "0|0|
Sd7VX;VR;Vs;A3"). Proof using H. exact (proj1 (proj2 (proj2 (proj2 (proj2 inv_meta))))). Qed.
  Lemma inv_usage : ltac2:(tb__ "0|0|
Sd8VX;VU;Vs;A3"). Proof using H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 inv_meta)))))). Qed.
  Lemma inv_reserved : ltac2:(tb__ "0|0|
Sd1VX;VR;Vs;A3"). Proof using H. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 inv_meta))))))). Qed.
  Lemma inv_partial : partial_unique X s. Proof using H. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 inv_meta))))))). Qed.
End Proj.

Definition WF (s : astate) : Prop := ltac2:(tb__ "0|0|
SbdS81S1A1S85S7aS1S0A2A1Sc1Vs;A4").

Lemma wf_init : WF init_state.
Proof.
  unfold WF.
  assert (NU : forall g am, ~ usedX [] init_state g am) by (intros g am H; unfold usedX, MTX, MT in H; cbn in H; discriminate).
  split.
  { unfold ctx_ok. cbn -[Z.le Z.lt Z.pow]. repeat split; try lia; try reflexivity;
      intros u Hu; apply repeat_spec in Hu; subst u; lia. }
  split.
  { unfold keys_ok, keys. cbn. split; [constructor|]. split; [intros p []|]. split; [reflexivity|]. split; [intros H; exfalso; exact (H eq_refl)|]. unfold METAS_PER_AREA. lia. }
  split.
  { unfold areas_ok. cbn -[Z.mul Z.pow Z.sub Z.le Z.lt]. split; [constructor|]. split; [intros a []|]. split; [reflexivity|]. split; [reflexivity|].
    split; [intros k rg Hk; unfold region_of in Hk; cbn in Hk; destruct k; discriminate|].
    split; [reflexivity|]. split; [reflexivity|]. split; [intros H; lia|].
    intros k rg Hk. unfold region_of in Hk. cbn in Hk. destruct k; discriminate. }
  split; [intros x []|].
  split; [intros g am H; exfalso; exact (NU g am H)|].
  split; [intros g1 a1 g2 a2 H; exfalso; exact (NU _ _ H)|].
  split; [intros g1 a1 g2 a2 H; exfalso; exact (NU _ _ H)|].
  split.
  { split; [|split].
    - exists []. split; [split; [split; [constructor | exact I] | reflexivity]|]. intros g pr nx H. unfold MTX, MT in H. cbn in H. discriminate.
    - intros sc Hsc. exists []. split.
      + unfold active_hd. cbn [st_active init_state]. rewrite nth_repeat. split; [split; [constructor | exact I] | reflexivity].
      + split; [intros q a Hq; exfalso; exact (NU q a Hq)|].
        split; [intros q a Hq; exfalso; exact (NU q a Hq)|].
        split; [intros q a Hq; exfalso; exact (NU q a Hq)|].
        intros q a Hq; exfalso; exact (NU q a Hq).
    - intros g am H. exfalso. exact (NU g am H). }
  split.
  { intros sc Hsc. unfold usage_of, class_sum, keys, U0. cbn [st_usage st_metas init_state map fold_right]. unfold znth. rewrite nth_repeat. reflexivity. }
  split; [intros g i H; discriminate|].
  intros g1 a1 g2 a2 H. exfalso. exact (NU _ _ H).
Qed.

Lemma image_init : ltac2:(tb__ "0|0|
S70S7eSa0A1Sc8S2fA1Sc4S2fA1A3").
Proof. vm_compute. reflexivity. Qed.

Lemma footprint_init : ltac2:(tb__ "0|1|
S70S7eS7aSa5S0A2M0A1Sb4S2fA1S7bG0S80Sa5S0Sa4Z0A1SbcA4S81G0A1A3A3").
Proof. reflexivity. Qed.

Lemma user_blocks_init : user_blocks init_state = [].
Proof. reflexivity. Qed.

Definition fold_off (slack off0 : Z) : Z := ltac2:(tb__ "0|2|
S78S0L_;M0S94Vslack;Voff0;A2S9bVslack;S9cVslack;Z1M1A2A2S0S9bR1S9cR1Z2A2A2S0S9bR1S9cR1Z4A2A2S0S9dVoff0;R1A2S0G0S94Vslack;R1A2S93R1S8dVslack;G1A2A2R1X78x2Toff1;Tm3;Tm2;Tm1;Voff0;X78x2").

Lemma fold_off_small_ok : ltac2:(tb__ "0|2|
S70S78S147S0S0S147S0S0Sc5R2R1A2S0S77S90Z0M0R1A2S90R1R3A2A2Toff;Loff0;Sa8G0Z100A2M1A3Lslack;G1A3S7fA3").
Proof. vm_compute. reflexivity. Qed.

Lemma fold_off_ok : ltac2:(tb__ "0|3|
S0S0S8eZ0M0R2A2M1S6fG1S92R2Z100A2A2S6fS8eG0Sc5R4R3A2M2A2S8eG2R4A2A2F_;F_;Foff0;Fslack;").
Proof.
  intros slack off0 Hs Ho.
  destruct (Z_lt_dec slack 256) as [Hlt|Hge].
  - assert (Hin : forall l k, 0 <= k < 256 ->
              forallb (fun x => let off := fold_off l x in (0 <=? off) && (off <=? l)) (zseq 0 256) = true ->
              0 <= fold_off l k <= l).
    { intros l k Hk Hf. rewrite forallb_forall in Hf.
      specialize (Hf k).
      assert (HIn : In k (zseq 0 256)).
      { unfold zseq. apply in_map_iff. exists (Z.to_nat k). split; [lia|]. apply in_seq. lia. }
      specialize (Hf HIn). cbn beta in Hf. apply andb_prop in Hf as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2. lia. }
    apply Hin; [lia|].
    pose proof fold_off_small_ok as HT. rewrite forallb_forall in HT. apply HT.
    unfold zseq. apply in_map_iff. exists (Z.to_nat slack). split; [lia|]. apply in_seq. lia.
  - unfold fold_off. destruct (slack <? off0) eqn:E; [apply Z.ltb_lt in E; lia|lia].
Qed.

Lemma class_of_units_ok : ltac2:(tb__ "0|1|
S70S78S147S0S0S62R1A1S0S77S77S77S90Z0M0R1A2S94R1Z30A2A2S94R2S4fR1S4dA2A2A2Sa9S94G0R1A2S90S4fS93R1Z1A2S4dA2R2A2A2A2Tc;Lk;Sa8G0Z1fffA2A3S7fA3").
Proof. vm_compute. reflexivity. Qed.

Lemma size_to_class_range : ltac2:(tb__ "0|2|
S0S6fS8eZ0M0R1A2S92R1S49A2A2S6fS6fS8eG0S6dR2A1M1A2S92G1Z30A2A2S8eS8dR2S25A2S36G1A1A2A2F_;Fn;").
Proof.
  intros n Hn. unfold size_to_class, class_size.
  set (k := Z.shiftr (n + IB - 1) 4).
  assert (Hk : 0 <= k < 8191).
  { subst k. rewrite Z.shiftr_div_pow2 by lia. unfold MMAP_THRESHOLD, IB in *.
    split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  pose proof class_of_units_ok as HT. rewrite forallb_forall in HT.
  specialize (HT k).
  assert (HIn : In k (zseq 0 8191)).
  { unfold zseq. apply in_map_iff. exists (Z.to_nat k). split; [lia|]. apply in_seq. lia. }
  specialize (HT HIn). cbn beta in HT.
  apply andb_prop in HT as [HT H4]. apply andb_prop in HT as [HT H3]. apply andb_prop in HT as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3.
  split; [lia|].
  assert (Hkn : n + IB <= UNIT * k + UNIT).
  { subst k. rewrite Z.shiftr_div_pow2 by lia. unfold UNIT, IB in *.
    pose proof (Z.mul_succ_div_gt (n + 4 - 1) (2 ^ 4) ltac:(lia)) as Hd. lia. }

  unfold UNIT in *. nia.
Qed.

Fixpoint regions_after (rs : list region) (tr : list (kreq * Z)) : list region :=
  match tr with
  | [] => rs
  | (KMmapRW len, z) :: t => regions_after (if z =? 0 then rs else rs ++ [mkRegion RkMap (page_round len) [] true]) t
  | (KMmapNone len, z) :: t => regions_after (if z =? 0 then rs else rs ++ [mkRegion RkMetaRes len [] true]) t
  | (KBrkGrow 2, z) :: t => regions_after (if z =? 0 then rs else rs ++ [mkRegion RkBrk (2 * PGSZ) [] true]) t
  | (KBrkGrow _, z) :: t =>
      regions_after rs t
  | (KMunmap r len, _) :: t => regions_after (lupd rs r (mkRegion RkMap (rg_len (nth r rs (mkRegion RkMap 0 [] false))) [] false)) t
  | _ :: t => regions_after rs t
  end.

Definition same_shape_regions (a b : list region) : Prop := ltac2:(tb__ "0|0|
S6fS70S7eS8A1S152S3S8S18Va;A4S152S3S8S18Vb;A4A3S70S7eS78A1S152S3S78S19Va;A4S152S3S78S19Vb;A4A3A2").

Module Conjectures.

Lemma free_null : ltac2:(tb__ "0|1|
S9S70S65S9S7aS8aS9A2M0A2S55S85S1A1R1A2S5cS9G0S80S8aS9S8cR1A4A3A3Fs;").
Proof. reflexivity. Qed.

End Conjectures.

Module Probes.

Fixpoint run_states (r : srun) (ops : list op) (acc : list astate) : list astate * option failure :=
  match ops with
  | [] => (rev acc, None)
  | o :: t => let r' := run_op r o in
              match sr_err r' with
              | Some e => (rev acc, Some e)
              | None => run_states r' t (sr_state r' :: acc)
              end
  end.

Definition states (ans : list (option Z)) (ops : list op) : list astate * option failure := ltac2:(tb__ "0|0|
S16cS68S2fS81S79S1A1A1S81S7aSdS0A2A1Vans;S85S1dA1A5Vops;S7bS9S2fS81S9A1A3A3").

Definition check (ans : list (option Z)) (ops : list op) : Z * bool * option failure := ltac2:(tb__ "0|3|
S7aS7eS9A1M0S79S1dA1M1A2S7aS7aS0S78A2M2G1A2Lx;S171Vans;Vops;A2G0G1S80G2G1S80S0S78S95S82S9R2A2A1S147S9S146R2A3A4R1A4Le;Ll;X7ax1").

Definition lcg (x : Z) : Z := ltac2:(tb__ "0|0|
S96S8dS91Vx;Z5851f42d4c957f2dA2Z14057b7ef767814fA2S97Z2Z40A2A2").
Definition probe_sizes : list Z := ltac2:(tb__ "0|0|
S7bS0Z1S7bS0Z8S7bS0Z10S7bS0Z18S7bS0Z28S7bS0Z64S7bS0Z70S7bS0Za0S7bS0Zc8S7bS0Z1ecS7bS0Z1f4S7bS0Z3e8S7bS0Z460S7bS0Z7d0S7bS0Z8d6S7bS0Zaa0S7bS0Zfa0S7bS0Z1000S7bS0Z1388S7bS0Z17a0S7bS0Z1c58S7bS0Z21fcS7bS0Z4060S7bS0Z8060S7bS0Z10060S7bS0Z186a0S7bS0Z1ffebS7bS0Z1ffecS7bS0Z20060S7bS0Z30d40S7bS0Z493e0S81S0A1A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3").

Fixpoint remove_nth (l : list nat) (k : nat) : list nat :=
  match l, k with
  | [], _ => []
  | _ :: t, O => t
  | h :: t, S k' => h :: remove_nth t k'
  end.

Fixpoint gen (fuel : nat) (seed : Z) (nm : nat) (live : list nat) (pfree : Z) (acc : list op) : list op :=
  match fuel with
  | O => rev acc
  | S f =>
    let r := lcg seed in
    let choice := (Z.shiftr r 33) mod 100 in
    if (choice <? pfree) && negb (Nat.eqb (length live) 0) then
      let k := Z.to_nat ((Z.shiftr r 17) mod Z.of_nat (length live)) in
      gen f r nm (remove_nth live k) pfree (Free (nth k live O) :: acc)
    else
      let sz := nth (Z.to_nat ((Z.shiftr r 41) mod Z.of_nat (length probe_sizes))) probe_sizes 16 in
      gen f r (S nm) (live ++ [nm]) pfree (Malloc sz :: acc)
  end.

Fixpoint gen_ans (fuel : nat) (seed : Z) (pr : Z) (acc : list (option Z)) : list (option Z) :=
  match fuel with
  | O => rev acc
  | S f =>
    let r := lcg seed in
    let c := (Z.shiftr r 29) mod 100 in
    gen_ans f r pr ((if c <? pr then Some 0 else if c <? pr + 20 then Some ((Z.shiftr r 13) mod 256) else None) :: acc)
  end.

Definition campaign (seeds : list Z) (nops : nat) (pfree pr : Z) : list (Z * bool * option failure) := ltac2:(tb__ "0|0|
S152S0S7aS7aS0S78A2S79S1dA1A2S0S166S168U7d0S8dR1Z7A2Vpr;S81S79S0A1A1A4S167Vnops;R1U0S81S7cA1Vpfree;S81S6A1A6A2Lsd;Vseeds;A4").

Fixpoint pingpong (n : nat) (k : nat) (sz : Z) : list op :=
  match n with O => [] | S n' => Malloc sz :: Free k :: pingpong n' (S k) sz end.

Definition bounce_script : list op := ltac2:(tb__ "0|6|
S87S6S161U78M0U0Z4e20M1A3S87S6S7bS6S3aG1A1M2S7bS6G2S7bS6G2S7bS6G2S7bS6S1aU7bA1S7bS6S1aG0A1S7bS6G2S7bS6G2S7bS6G2S7bS6S1aU79A1S7bS6S1aU7aA1S7bS6S1aU7cA1S7bS6S1aU7dA1S7bS6S1aU7eA1S7bS6G2S7bS6S3aZ4650A1S7bS6G2S7bS6S1aU80A1S7bS6S1aU7fA1S7bS6S1aU81A1S7bS6G2S7bS6G2S7bS6S1aU82A1S81S6A1M3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3A3S87S6S161U28U84Z1388M4A3S7bS6S3aG4A1M5S7bS6G5S7bS6S1aUacA1S7bS6G5S7bS6S1aUadA1S7bS6S1aUaeA1G3A3A3A3A3A3A3A3A3A3").

Example wf_vec1 : check [] vec1_prefix = (23, true, None).
Proof. vm_compute. reflexivity. Qed.
Example wf_hdr_script : check [] hdr_script = (47, true, None).
Proof. vm_compute. reflexivity. Qed.
Example wf_bounce : check [] bounce_script = (350, true, None).
Proof. vm_compute. reflexivity. Qed.

Example wf_refusals :
  map (fun ao => check (fst ao) (snd ao))
    [([grant; refuse], [Malloc 4096; Malloc 100; Free 0; Free 1]);
     ([grant; grant; grant; refuse], [Malloc 4096; Malloc 4096; Free 1]);
     ([grant; grant; refuse; refuse], [Malloc 200000; Malloc 10; Malloc 200000; Free 2; Free 1]);
     ([grant; refuse; grant; refuse; refuse; grant], [Malloc 10; Malloc 10; Malloc 5000; Free 2; Free 1])]
  = [(5, true, None); (4, true, None); (6, true, None); (6, true, None)].
Proof. vm_compute. reflexivity. Qed.

Example wf_random : campaign [23] 300 50 10 ++ campaign [31] 300 70 30
                    = [(301, true, None); (301, true, None)].
Proof. vm_compute. reflexivity. Qed.

Definition st1 : astate := ltac2:(tb__ "0|1|
S6eS6aS81S79S0A1A1S7bS6S3aZ64A1M0S7bS6G0S7bS6S3aZ1388A1S7bS6S3aZ30d40A1S7bS6S1aU0A1S81S6A1A3A3A3A3A3A2A1").

Definition first_used (s : astate) : option (sptr * ameta) := hd_error (used_metas s).

Example wf_mutations :
  (wfb st1,

   wfb (set_usage (zset 6 (usage_of st1 6 + 1) (st_usage st1)) st1),

   match first_used st1 with
   | Some (g, am) => wfb (set_metas (mupdate (st_metas st1) g (MUsed (am_set_freed (Z.lor (am_freed am) 2) am))) st1)
   | None => true
   end,

   wfb (set_active (lupd (st_active st1) 6%nat (Some (SP 0 0))) st1),

   wfb (set_brk BrkNever st1))
  = (true, false, false, false, false).
Proof. vm_compute. reflexivity. Qed.

Example st1_blocks :
  user_blocks st1 = [(SP 1 176, 100); (SP 2 48, 5000); (SP 3 64, 200000)]
  /\ footprint st1 = [(LCtx 0, 928); (LMem (SP 0 4096), 4096); (LMem (SP 1 0), 4096);
                      (LMem (SP 2 0), 16384); (LMem (SP 3 0), 200704)].
Proof. vm_compute. split; reflexivity. Qed.

Definition frames_ok (s : astate) : bool := ltac2:(tb__ "0|5|
S147S7aS7aS7aS1S2A2M0S0A2M1S5A2M2G2G2S78Lf;R1G1S5G1S78Lp;R2G0S0G0S78Lp0;R2S1S2S77S10fS10aR1R3R5A3M3ScR1A1S13aVs;R2R1R3R5A5A3S79S7aS1S0A2M4A1S78Lx;S63S1fVs;A1G3A2G4G4S78Lp;R1S1S0S77S15R5R2A2S8fR6R1A2A2Li';Lg';X7ax1Lp;S7dX79x2A2Lam;Lg;X7ax1Li;Lp0;X7ax1Lfr;Lp;X7ax1Lf;S10bVs;A1A3").

Example get_meta_probe :
  (frames_ok st1, let '(l, _) := states [] bounce_script in forallb frames_ok l,
   let '(l, _) := states (gen_ans 2000 30 10 []) (gen 300 23 O [] 50 []) in forallb frames_ok l)
  = (true, true, true).
Proof. vm_compute. reflexivity. Qed.

Fixpoint irun2 {A} (fuel : nat) (t : itree astate A) (kans jans : list (option Z)) (tr : list (kreq * Z))
  : outcome A * list (kreq * Z) * list (option Z) * list (option Z) :=
  match fuel with
  | O => (OStarved, rev tr, kans, jans)
  | S f =>
    match t with
    | IRet a => (ODone a, rev tr, kans, jans)
    | IFail e => (OFailed e, rev tr, kans, jans)
    | IAsk q _ k =>
        match q with
        | KJunk pristine =>
            let z := match hd None jans with Some z => z | None => pristine end in
            irun2 f (k z) kans (tl jans) ((q, z) :: tr)
        | _ =>
            let z := match hd None kans with Some z => z | None => 1 end in
            irun2 f (k z) (tl kans) jans ((q, z) :: tr)
        end
    end
  end.

Record srun2 := mkRun2 { s2_state : astate; s2_ptrs : list (option sptr); s2_trace : list (kreq * Z);
                         s2_kans : list (option Z); s2_jans : list (option Z); s2_err : option failure;
                         s2_hist : list astate }.

Definition run_op2 (r : srun2) (o : op) : srun2 := ltac2:(tb__ "0|1c|
S79S1dA1S158Lx;S15bVr;A1S1dVr;Lf;S6S7aS7aS7aS3bS7aS79S79S1A1M0A1M1S9A2M2A1M3S7eS7aSdS0A2M4A1M5A2M6S7eS79S0A1A1M7A2M8G7A2M9Lo;Vo;S0S7aS7aS7aS3bS7aG0S9A2MaA1MbG5A2McG7A2MdG7A2G9Lx;S15fGaU3e8MeS66R1S16fVr;A1MfA2S16eVr;A1M10S16dVr;A1M11S81G4A1M12A6GdG7GdG9Lp0;R2GcG7GcG9Lp1;R2GbG5GbG9Lo0;R2GaGaG9La;R1G0S9S80G8G7S80G6G7S80G3G5S53G2S80G1S9S83G0R2A2R1A4A2R4A4R6A4R8A4Ls';Lp;X7ax1La;S1dS80G8G7S80G6G7S80G3G5S5eG2R1A2R2A4R4A4R6A4Le;M13S80G8G7S80G6G7S80G3G5S5fG2A1R1A4R3A4R5A4M14X3bx3Ltr;Lo0;X7ax1Lka;Lp1;X7ax1Lja;Lp0;X7ax1Ln;S7cS7aS7aS7aS3bS7aS8aS9A2M15A1M16G5A2M17G7A2M18G7A2G9Lx;S15fG15GeS55S153G0R1S15dVr;A1M19S85S1A1A4GfA2G10G11G12A6G18G7G18G9Lp;R2G17G7G17G9Lp0;R2G16G5G16G9Lo0;R2G15G15G9La;R1S8aS9S80G8G7S80G6G7S80G3G5S53G2S80G1S9S85G0A1R1A4A2R4A4R6A4R8A4Ls';Lu;X7ax1La;G13G14X3bx3Ltr;Lo0;X7ax1Lka;Lp0;X7ax1Lja;Lp;X7ax1Lk;X6x2G9G9S158Lstep;R1G8G7G8S158Lp;R2G6G7G6S158Lp0;R2G3G5G3S158Lo0;R2G2G2S158La;R1G1S9S15aR1G1S7eG0A1Lnp;R2G0S87G0G19S7bG0R1S81G0A1A3A3Lp;G19X79x2S87G4S15eVr;A1M1aR4A3R6R8S85S1dA1S87S9S15cVr;A1M1bS7bS9R1S81S9A1A3A3A7Ls';Lnp;X7ax1La;S1dS15aGfG19S87G4G1aR2A3R4R6S83S1dR1A2G1bA7Le;S15aGfG19S87G4G1aR1A3R3R5S83S1dS5aA2G1bA7X3bx3Ltr;Lo0;X7ax1Lka;Lp0;X7ax1Lja;Lp;X7ax1Tstep;X79x2").

Definition run_script2 (kans jans : list (option Z)) (ops : list op) : srun2 := ltac2:(tb__ "0|0|
S151S158S6S16bVops;S15aS2fS81S79S1A1A1S81S7aSdS0A2A1Vkans;Vjans;S85S1dA1S7bS9S2fS81S9A1A3A7A5").

Definition kernel_only (tr : list (kreq * Z)) : list (kreq * Z) := ltac2:(tb__ "0|2|
S14fS7aSdS0A2M0G0SdS78Lx;S86SdS0R1A3S7fS0S7fLnpages;S7fS0S7fLlen;M1G1S1S7fLpage;S7cG1Lr;S0S7dLpristine;Xdx8Lqz;Vtr;A3").

Definition listZ_eqb (a b : list Z) : bool := ltac2:(tb__ "0|1|
S77S157S82S0Va;A2S82S0Vb;A2A2S147S7aS0S0A2M0G0S8fS86S0S0R1A3S84S0S0R1A3A2Lp;S14aS0S0Va;Vb;A4A3A2").
Definition slot_eqb (a b : slotst) : bool := ltac2:(tb__ "0|7|
S77S79S7aS0S0A2M0A1S78Lx;M1S31Va;A1G0G0S78Lp;R1S0S0G1S31Vb;A1M2G0G0S78Lp0;R1S0S0S77S8fR5R2A2S8fR4R1A2A2Ly2;Lx2;X7ax1Lp0;S7dX79x2Ly1;Lx1;X7ax1Lp;G1G2G0S7dLp;S7fX79x2X79x2S79S5A1S78Lx;M3S16Va;A1S5G3S16Vb;A1M4S5S77S77S8fS24R2A1S24R1A1A2S8fS23R2A1S23R1A1A2A2SeS78Lx;M5S1eR2A1G5S1eR1A1M6S7fS7dXex2G5G6S7dS7fXex2Xex2A2Lf2;S7dX79x2Lf1;G3G4S5S7dLf;S7fX79x2X79x2A2").
Definition ameta_eqb (a b : ameta) : bool := ltac2:(tb__ "0|3|
S77S77S77S77S77S77S77S77S77S77S13S29Va;A1S29Vb;A1A2S13S28Va;A1S28Vb;A1A2A2S15ScVa;A1ScVb;A1A2A2S8fS21Va;A1S21Vb;A1A2A2S8fS22Va;A1S22Vb;A1A2A2S8fSaVa;A1SaVb;A1A2A2S8fSfVa;A1SfVb;A1A2A2S8fS11Va;A1S11Vb;A1A2A2S8fS2eVa;A1S2eVb;A1A2A2S157S82S14S3eVa;A1M0A2S82S14S3eVb;A1M1A2A2A2S147S7aS14S14A2M2G2S170S86S14S14R1A3S84S14S14R1A3A2Lp;S14aS14S14G0G1A4A3A2").
Definition mslot_eqb (a b : mslot) : bool := ltac2:(tb__ "0|4|
S4S78La;Va;S79S1A1M0G0S4S78Lb;M1Vb;G0G0S77S13R4R2A2S13R3R1A2A2Ln2;Lp2;S7dS2S7dLm;M2X4x3Ln1;Lp1;G1Vb;G0G0S7dLnext;Lprev;M3S7fG2X4x3S2G1Vb;G3S7dS2S164R2R1A2Ly;X4x3Lx;X4x3").
Definition region_eqb (a b : region) : bool := ltac2:(tb__ "0|2|
S77S77S77S8S78Lx;M0S18Va;A1G0S18Vb;A1M1S7fS7dS7dX8x3G0G1S7dS7fS7dX8x3G0G1S7dS7dS7fX8x3X8x3S8fS1bVa;A1S1bVb;A1A2A2S174S19Va;A1S19Vb;A1A2A2S159S37Va;A1S37Vb;A1A2A2").
Definition brk_eqb (a b : brkst) : bool := ltac2:(tb__ "0|2|
S10S78La;Va;S10S78Lb;M0Vb;S7fS7dS7cS0S7dLpages;Lr;M1X10x3G0Vb;S7dS7fG1X10x3S7cS0G0Vb;S7dS7dS7cS0S77S157R4R2A2S8fR3R1A2A2Lp';Lr';X10x3Lp;Lr;X10x3").
Definition astate_eqb (a b : astate) : bool := ltac2:(tb__ "0|10|
S77S77S77S77S77S77S77S77S77S77S77S77S77S77S77S77S77S77S77S77S77S77S174S43Va;A1S43Vb;A1A2S8fS44Va;A1S44Vb;A1A2A2S13S3cVa;A1S3cVb;A1A2A2S15S41Va;A1S41Vb;A1A2A2S8fS33Va;A1S33Vb;A1A2A2S8fS2cVa;A1S2cVb;A1A2A2S8fS2dVa;A1S2dVb;A1A2A2S13S3fVa;A1S3fVb;A1A2A2S13S40Va;A1S40Vb;A1A2A2S15S38Va;A1S38Vb;A1A2A2S157S82S79S1A1M0S32Va;A1M1A2S82G0S32Vb;A1M2A2A2A2S147S7aG0G0A2M3G3S13S86G0G0R1A3S84G0G0R1A3A2Lp;S14aG0G0G1G2A4A3A2S159S47Va;A1S47Vb;A1A2A2S159S46Va;A1S46Vb;A1A2A2S159S42Va;A1S42Vb;A1A2A2S8fS45Va;A1S45Vb;A1A2A2S165S34Va;A1S34Vb;A1A2A2S157S82S7aS1S4A2M4S1fVa;A1M5A2S82G4S1fVb;A1M6A2A2A2S147S7aG4G4A2M7G7S77S15S86S1S4S86G4G4R1A3M8A3S86S1S4S84G4G4R1A3M9A3A2S169S84S1S4G8A3S84S1S4G9A3A2A2Lp;S14aG4G4G5G6A4A3A2S157S82S3S2bVa;A1MaA2S82S3S2bVb;A1MbA2A2A2S147S7aS3S3A2McGcS16aS86S3S3R1A3S84S3S3R1A3A2Lp;S14aS3S3GaGbA4A3A2S157S82S1S17Va;A1MdA2S82S1S17Vb;A1MeA2A2A2S147S7aS1S1A2MfGfS15S86S1S1R1A3S84S1S1R1A3A2Lp;S14aS1S1GdGeA4A3A2").

Fixpoint states_eqb (l1 l2 : list astate) : bool :=
  match l1, l2 with
  | [], [] => true
  | a :: t1, b :: t2 => astate_eqb a b && states_eqb t1 t2
  | _, _ => false
  end.

Definition kreq_eqb (q1 q2 : kreq) : bool := ltac2:(tb__ "0|7|
SdS78Lq1;Vq1;SdS78Lq2;M0Vq2;S7fS0S7dLnpages;M1S7dS0S7dLlen;M2G2S1S7dLpage;M3S7cG2Lr;M4S0S7dLpristine;M5Xdx8S0G0Vq2;S7dS0S8fR2R1A2Ly;M6S7dG2G2G3G4G5Xdx8Lx;G0Vq2;S7dG1S7fG2G2G3G4G5Xdx8S0G0Vq2;S7dG1S7dG6G2G3G4G5Xdx8Lx;S0G0Vq2;S7dG1S7dG2G6G3G4G5Xdx8Lx;S1G0Vq2;S7dG1S7dG2G2S1S15R2R1A2Lp';G4G5Xdx8Lp;S7cS0G0Vq2;S7dG1S7dG2G2G3S7cS0S77S157R4R2A2S8fR3R1A2A2Ll';Lr';G5Xdx8Ll;Lr;S0G0Vq2;S7dG1S7dG2G2G3G4G6Xdx8Lx;Xdx8").

Fixpoint trace_eqb (a b : list (kreq * Z)) : bool :=
  match a, b with
  | [], [] => true
  | (q1, z1) :: t1, (q2, z2) :: t2 => kreq_eqb q1 q2 && (z1 =? z2) && trace_eqb t1 t2
  | _, _ => false
  end.

Fixpoint gen_junk (fuel : nat) (seed : Z) (acc : list (option Z)) : list (option Z) :=
  match fuel with
  | O => rev acc
  | S f => let r := lcg seed in gen_junk f r (Some ((Z.shiftr r 21) mod 256) :: acc)
  end.
Fixpoint gen_kans (fuel : nat) (seed : Z) (pr : Z) (acc : list (option Z)) : list (option Z) :=
  match fuel with
  | O => rev acc
  | S f => let r := lcg seed in gen_kans f r pr ((if (Z.shiftr r 29) mod 100 <? pr then Some 0 else None) :: acc)
  end.

Definition shape_probe (kans jans1 jans2 : list (option Z)) (ops : list op) : ltac2:(tb__ "0|0|
S7aS7aS7aS7aS7aS7aS78S0A2S78A2S78A2S78A2S78A2S0A2") := ltac2:(tb__ "0|e|
S162Vkans;Vjans1;Vops;A3S158S162Vkans;Vjans2;Vops;A3S158S80S7aS7aS7aS7aS7aS78S0A2M0S78A2M1S78A2M2S78A2M3S78A2S0S80G3S78S80G2S78S80G1S78S80G0S78S80S78S0S79S1dA1S78Lx;M4S15bR2A1S1dS7dLf;M5G4S15bR1A1G5S7fX79x2X79x2S95S82S9S15cR2A1M6A2A1A4S172S160S15eR2A1M7A1M8S160S15eR1A1A1A2A4S163S152S9S9Sb3G6A4S152S9S9Sb3S15cR1A1M9A4A2A4S88S163G6G9A2A1A4S147S7aS79S1A1MaGaA2MbGbGaS78Lx;McS86GaGaR1A3S1GcS84GaGaR2A3S1S7fLs0;S7dX79x2Ls;GcS84GaGaR1A3S1S7dLs;S7fX79x2X79x2Lp;S14aGaGaS15dR2A1S15dR1A1A4A3A4S95S176S82S7aSdS0A2MdG7A2S82GdG8A2A2A1A4Tr2;Tr1;").

Example shape_eq_probe :
  map (fun sd => shape_probe (gen_kans 3000 (sd + 3) 10 []) (gen_junk 500 (sd + 100) []) (gen_junk 500 (sd + 200) [])
                             (gen 300 sd O [] 50 []))
      [21; 44]
  = [(true, 301, true, true, true, true, 19); (true, 301, true, true, true, true, 19)].
Proof. vm_compute. reflexivity. Qed.

Definition no_single_slot_map (sc : Z) : bool := ltac2:(tb__ "0|5|
S0S6bS156S0R1U20A3S2fA2Lb;S0S9Fb;S36Vsc;A1S0S78S0L_;S8fVsc;Z0M0A2G0S8dS93S36S93Vsc;Z1M1A2A1S25A2G1A2X78x2S0S93R2S25A2S0S14fS0S0S77S90R3R1A2S90R1R2A2A2Lr;S7bS0R2S7bS0R1S149S0S0S0S7bS0S93S91S7R1A2M2Z15A2S7bS0S93G2Z14A2S7bS0S93G2Z13A2S81S0A1A3A3A3Lk;Sa8G1Z3A2A4A3A3A3S7eS0A1S147S0S0S58S59Vsc;R1S156S0G0U30A3M3A3R6G0A1A2S9S58S59Vsc;R2G3A3R7Z96A1A2S9S64Vsc;R3A2S0S78S78L_;S94S9aS7Z2M4A2S8dS91R8R1A2S12A2A2S147S0S0S77S90G4S86S0S0S56R4Vsc;R1R2R5A5A3A2S90G4S86S0S0S56R3Vsc;R1R2R5A5A3A2A2Lreq;R5A3S7fX78x2Tcnt0;Ts';Ts;Lusage;Sa8G0Z8dA2A3Tcands;Thi;Tlo;Tsize;Tst_b;").

Example no_single_slot_map_le_26 : forallb no_single_slot_map (zseq 0 27) = true.
Proof. vm_compute. reflexivity. Qed.

End Probes.
