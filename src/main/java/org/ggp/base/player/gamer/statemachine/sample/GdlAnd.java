package org.ggp.base.player.gamer.statemachine.sample;

import java.util.List;

import org.ggp.base.util.gdl.grammar.GdlLiteral;

@SuppressWarnings("serial")
public final class GdlAnd extends GdlLiteral
{

    private final List<GdlLiteral> conjuncts;
    private transient Boolean ground;

    GdlAnd(List<GdlLiteral> conjuncts)
    {
        this.conjuncts = conjuncts;
        ground = null;
    }

    public int arity()
    {
        return conjuncts.size();
    }

    private boolean computeGround()
    {
        for (GdlLiteral literal : conjuncts)
        {
            if (!literal.isGround())
            {
                return false;
            }
        }

        return true;
    }

    public GdlLiteral get(int index)
    {
        return conjuncts.get(index);
    }

    public List<GdlLiteral> getConjuncts() {
        return conjuncts;
    }

    @Override
    public boolean isGround()
    {
        if (ground == null)
        {
            ground = computeGround();
        }

        return ground;
    }

    @Override
    public String toString()
    {
        StringBuilder sb = new StringBuilder();

        sb.append("( and ");
        for (GdlLiteral literal : conjuncts)
        {
            sb.append(literal + " ");
        }
        sb.append(")");

        return sb.toString();
    }

}