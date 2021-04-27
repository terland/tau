LoadPackage("qpa");
LoadPackage("yags");
Q := Quiver(3, [[1,2,"a"],[1,2,"b"],[2,1,"c"],[2,1,"d"],[2,3,"e"],[2,3,"f"],[3,2,"g"],[3,2,"h"],[3,1,"i"],[3,1,"j"],[1,3,"k"],[1,3,"l"] ] );


Display(Q);

KQ := PathAlgebra(GF(2),Q);

AssignGeneratorVariables(KQ);


stop := 1;

rels := [];
AddNthPowerToRelations(KQ,rels,2);

KQ := KQ/rels;

#/rels;
#KQ := KQ/[x1*x2,x2*x1,y1*y2,y2*y1,x1*y2-y2*x1,x2*y1-y1*x2];

#/[a*b];

LeftMutation := function(x,u)
    local g, y, test;
    g := LeftApproximationByAddM(x,u);
    Display("approximation ok");
    y := CoKernel(g);
    Display("Cokernel ok");
    
    
    test := MaximalCommonDirectSummand( u, y );
    
    # TODO: resolve this mess!
    Display(FamilyObj(test));
    return y;
    
    Display("test-module ok");
   
    if  not test then
        Display("returning");
        return y;
    fi;
       

    while Dimension( test[ 1 ] ) <> 0 do
          test := MaximalCommonDirectSummand( u, test[ 3 ] );
          Display("get out");
    od;
    
    
    
    return test[ 3 ];
end;



proj := IndecProjectiveModules(KQ);

LeftMutation_new := function(x,u)
    local g, y, test;
    g := LeftApproximationByAddM(x,u);
    y := CoKernel(g);
    #test := MaximalCommonDirectSummand( u, y );
    #while Dimension( test[ 1 ] ) <> 0 do
    #      test := MaximalCommonDirectSummand( u, test[ 3 ] );
    #od;
       
    return y;
    #return test[ 3 ];
end;


LeftMutation_old := function(x,u)
    local g,y;
    g := MinimalLeftApproximation(x,u);
    Display("approx OK");
    y := CoKernel(g);
    
    return y;
end;

LeftMutateOnList := function(m,i)
    local j,u,x,y;
    
    j := 1;
    u := [];
        
    while j <= Length(m) do
        if not j = i then
            #Display(m);
            #Display(m[j]);
            Add(u,m[j]);
        fi;
        j := j + 1;
        
    od;
        
    x := m[i];
    
    Display("doing-mutation");
    y := LeftMutation(x,DirectSumOfQPAModules(u));
    return y;
end;

GetMutation_children := function(mf)    
    local i,y,allmut,n,j,m,all_mutations;
    
    m := ShallowCopy(mf);
    
    i := 1;
    allmut := [];
    
    
    if (Length(m) < Length(proj)) then
        return [];
    fi;
    
    while i <= Length(m) do
        y := LeftMutateOnList(m,i);
        
        if y = [] then
            i := i + 1;
            continue;
        fi;
        
        
        
        if IsomorphicModules(y,m[i]) then
            #TODO: Collect bug/weird example from here.
            Display("???");
        fi;
        
        if not IsomorphicModules(y,ZeroModule(KQ)) then
            
            if not IsTauRigidModule(y) then
                i := i +1;
                continue;
            fi;
            #Display(i);
            #Display(m);
            #Display(y);
            n := ShallowCopy(m);
            n[i] := y;
            
            #Display(n);
            
            if IsomorphicModules(n[i],m[i]) then
                Display("returning!");
                return [];
            fi;
            
            if not IsTauRigidModule(DirectSumOfQPAModules(n)) then
                i := i +1;
                continue;
            fi;
            
            Add(allmut,n);
        fi;
        
        
        
        i := i + 1;
    od;
    
    return allmut;
    
end;

GetBoundedMutations := function(tau_tilt,depth,i,nogo)
    local j,y,mutation_j,all_mutations;

    if i > depth then
        return [];
    fi;
    
    all_mutations := [];
    
    j := 1;
    while j <= Length(tau_tilt) do
        
        if j = nogo then
            j := j + 1;
            continue;
        fi;
        
        y := LeftMutateOnList(tau_tilt,j);
        if not IsTauRigidModule(y) then
            j := j + 1;
            continue;
        fi;
        
        mutation_j := ShallowCopy(tau_tilt);
        mutation_j[j] := y;
        
        Add(all_mutations,mutation_j);
        Append(all_mutations,GetBoundedMutations(mutation_j,depth,i+1,j));
        
        Add(all_mutations,mutation_j);
        # Fix recursion
        
        j := j + 1;
    od;
    
    return all_mutations;
end;
    

GetMutations := function(mf, depth)    
    local i,y,allmut,n,j,m;
    
    Display(depth);
    
    if depth > 2 then
        return [];
    fi;
    
    m := ShallowCopy(mf);
    
    i := 1;
    allmut := [];
    Add(allmut,m);
    
    if (Length(m) < Length(proj)) then
        return [];
    fi;
    
    while i <= Length(m) do
    
        Display("computing..");
        y := LeftMutateOnList(m,i);
        #Display(y);
        Display("ok");
        
        if y = [] then
            i := i + 1;
            continue;
        fi;
        
        
        
        if IsomorphicModules(y,m[i]) then
            #TODO: Collect bug/weird example from here.
            Display("???");
        fi;
        
        Display("iso-test OK");
        
        if not IsomorphicModules(y,ZeroModule(KQ)) then
            
            if not IsTauRigidModule(y) then
                i := i +1;
                continue;
            fi;
            
            Display("tau-rigid test ok");
            #Display(i);
            #Display(m);
            #Display(y);
            n := ShallowCopy(m);
            n[i] := y;
            
            #Display(n);
            
            if IsomorphicModules(n[i],m[i]) then
                Display("returning!");
                return [];
            fi;
            
            
            if not IsTauRigidModule(DirectSumOfQPAModules(n)) then
                i := i +1;
                continue;
            fi;
            
            Display("tau-rigid dobbel test ok");
            
            
            Append(allmut,GetMutations(n,depth+1));
        fi;
        
        
        
        i := i + 1;
    od;
    
    return allmut;
    
end;

# Are two tau-tilting modules given as lists isomorphic?
EqualUpToOrder := function(m,n)
    local i;
    if not Length(m) = Length(n) then
        return False;
    fi;
    
    g := SymmetricGroup(Length(m));
    
    for p in g do
        lp := ListPerm(p,Length(m));
        
        m2 := [];
        for i in lp do
            Add(m2,m[i]);
        od;
        
        # iso?
        i := 1;
        alliso := true;
        while i <= Length(m2) do
            if not IsomorphicModules(m2[i],n[i]) then
                alliso := false;
            fi;
            
            i := i + 1;
        od;
        
        if alliso then
            return true;
        fi;
        
    od;
    
    return false;
end;

# IS t a TF-admissible (Treffinger, Mendoza) ordering of some module?
TFO := function(t)
    i := 1;
    while i < Length(t) do
        j := i + 1;
        
        allrest := [];
        while j <= Length(t) do
            Add(allrest,t[j]);
            j := j + 1;
        od;
        
        restmodule := DirectSumOfQPAModules(allrest);
        if (IsSurjective(TraceOfModule(restmodule,t[i]))) then
            return false;
        fi;
        i := i + 1;
        
    od;
    
    return true;
end;

# Find all TF-admissible orderings
AllTF := function(m)
    local g,lp,candidate,ans;
    g := SymmetricGroup(Length(m));
    ans := [];
    
    for perm in g do
        lp := ListPerm(perm,Length(m));
        candidate := [];
        for i in lp do
            Add(candidate,m[i]);
        od;
        
        if TFO(candidate) then
            Add(ans,candidate);
        fi;
    od;
    
    return ans;
end;

# Compute complete tau-exceptional sequence given a tf-ordered module
TauSequence := function(m)
    local ans,i,j,cml,cm,t;
    
    ans := [];
    i := 1;
    while i <= Length(m) do
        j := i + 1;
        cml := [];
        while j <= Length(m) do
            Add(cml,m[j]);
            j := j + 1;
        od;
        
        if (i = Length(m)) then
            Add(ans,m[i]);
            return ans;
        fi;
        
        cm := DirectSumOfQPAModules(cml);
        t := CoKernel(TraceOfModule(cm,m[i]));
        Add(ans,t);
        i := i + 1;
    od;
    
    return ans;
end;



TauRel := function(x,y)
    local n,i,j,k,z,all_corr;
    
    n := Length(x);
    
    i := 1;
    while i <= n do
        j := 1;
        while j <= n do
            z := ShallowCopy(x);
            z[i] := z[j];
            z[j] := x[i];
            
            k := 1;
            all_corr := true;
            while k <= Length(x) do
                if not k = j then
                    if not z[k] = y[k] then
                        all_corr := false;
                    fi;
                fi;
                
                k := k + 1;
            od;
            
            if all_corr then
                return true;
            fi;
            
            j := j + 1;
        od;
        
        i := i + 1;
    od;
    
    return false;
end;


TauRel2 := function(x,y)
    local n,i,j,k,z,all_corr;
    
    n := Length(x);
    
    i := 1;
    while i < n do
        j := i+1;
        
        z := ShallowCopy(x);
        z[i] := x[j];
        z[j] := x[i];
        
        #Display(z[i]);
            
        k := 1;
        all_corr := true;
        while k <= Length(x) do
            if not k = j then
                if not z[k] = y[k] then
                    all_corr := false;
                fi;
            fi;
            
            k := k + 1;
        od;
            
        if all_corr then
            return true;
        fi;
            
        i := i + 1;
    od;
    
    return false;
end;


btau := GetBoundedMutations(proj,1,1,-1);
Display(btau);

tautilting := GetMutations(proj,1);

#tautilting := [[proj[1],proj[2]]];
uniquetau := [];

Add(uniquetau,tautilting[1]);

# Remove duplicates
i := 2;
while i <= Length(tautilting) do
    Display(i);
    j := 1;
    new := true;
    while j <= Length(uniquetau) do
        if EqualUpToOrder(tautilting[i],uniquetau[j]) then
            new := false;
        fi;
        
        j := j + 1;
    od;
    
    if new then
        Add(uniquetau,tautilting[i]);
    fi;
        
    i := i + 1;
    
od;

all_tfo := [];

for m in uniquetau do
    Append(all_tfo, AllTF(m));
od;

Display(all_tfo);


all_tau := [];
tau_i := 1;
tau_to_tf := [];
for n in all_tfo do
    y := TauSequence(n);
    Add(all_tau,y);
    Add(tau_to_tf,[tau_i,y,n]);
    tau_i := tau_i + 1;
od;

# Build exchange graph for tau-exceptional sequences

ed := [];
i := 1;
while i <= Length(all_tau) do
    j := i + 1;
    while j <= Length(all_tau) do
        if TauRel2(all_tau[i],all_tau[j]) then
            Add(ed,[i,j]);
            #Add(ed,[j,i]);
        fi;
        j := j + 1;
    od;
    
    i := i + 1;
od;

SetDefaultGraphCategory(OrientedGraphs);
#g := GraphByEdges(ed);
#Draw(g);



# Generate partial mutation graph
e := [];
v := [];
computed := [];


add_layer := function(parent)
    for i in GetMutation_children(v[parent]) do
        
        found := false;
        cand := 1;
        while cand <= Length(v) do
            if i = v[cand] then
                Add(e,[parent,cand]);
                Display("Cycle!");
                found := true;
            fi;
            
            cand := cand + 1;
        od;
        
        if not found then
            Add(v,i);
            Add(e,[parent,Length(v)]);
        fi;
    od;
    
    Add(computed, parent);
end;

Add(v,proj);

compute_new_layer := function()
    local i,k,j,found;
    i := 1;
    k := Length(v);
    while i <= k do
        found := false;
        
        j := 1;
        while j <= Length(computed) do
            if j = i then
                found := true;
            fi;
            
            j := j + 1;
        od;
        
        if not found then   
            add_layer(i);
        fi;
        
        i := i + 1;
    od;
end;

compute_new_layer();

d := GraphByEdges(e);
#Draw(d);

number_of_tf := [];

for m in v do
    Add(number_of_tf,Length(AllTF(m)));
od;

for i in number_of_tf do
    if not i = 0 then
        Display(24/i);
    fi;
od;

e := [];

right_mutate := function(atseq)
    local j,nums;
    j := 1;
    nums := 0;
    Display(tau_to_tf[atseq][3]);
    Display(all_tau[atseq]);
    while j <= Length(all_tau) do
        if TauRel2(all_tau[atseq],all_tau[j]) then
            Add(e,[atseq,j]);
            Display(j);
            Display(all_tau[j]);
            nums := nums + 1;
            
        fi;
        j := j + 1;
    od;
    
    #Display("done");
    return nums;
end;

gvector := function(m)
    local pr,p1,p2,d_p1,d_p2,g_1,g_2;
    
    pr := ProjectiveResolution(m);
    p1 := Source(pr^1);
    p2 := Range(pr^1);
    
    # GET TOP OF MODULE HERE.

    return DimensionVector(TopOfModule(p2)) - DimensionVector(TopOfModule(p1));
end;

left_mutate := function(atseq)
    local j,nums;
    j := 1;
    nums := 0;
    Display(tau_to_tf[atseq][3]);
    Display(all_tau[atseq]);
    while j <= Length(all_tau) do
        if TauRel2(all_tau[j],all_tau[atseq]) then
            Display(j);
            Display(tau_to_tf[j][3]);
            Display(all_tau[j]);
            nums := nums + 1;
        fi;
        j := j + 1;
    od;

    #Display("done");
    return nums;
end;

i := 1;
while i <= Length(all_tau) do
    Display("right:");
    #Display(right_mutate(i));
    Display(left_mutate(i));
    i := i + 1;
od;

mutation_mat := [];

right_mutate_record := function()
    local j,nums,row,atseq;
    atseq := 1;
    

    
    while atseq <= Length(all_tau) do
    
        row := [];
        
        
        j := 1;
        while j <= Length(all_tau) do
        
            Add(row,0);
            
            if TauRel2(all_tau[atseq],all_tau[j]) then
                row[j] := 1;
                Display(atseq);
                Display(j);
                Display(row);
                fi;
            
            j := j + 1;
            
            od;
            
        Add(mutation_mat,row);
        atseq := atseq + 1;
        
        od;

end;

#d := GraphByEdges(e);
#Draw(d);


# Find all tau-tilting modules using left mutation. This will work in general in the tau-tilting finite case. 

